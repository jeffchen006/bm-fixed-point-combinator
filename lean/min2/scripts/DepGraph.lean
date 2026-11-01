import Lean
import TBeta.Main
open Lean Meta

/-! Walk the constants that `TBeta.no_fixed_point_combinator` really uses. Writes `logs/dep_used.tsv`, `logs/dep_all.tsv`. -/

def interesting (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m := env.header.moduleNames[idx.toNat]!
  if (`TBeta).isPrefixOf m || (`LeanJudge).isPrefixOf m then some m else none

/-- `foo._proof_1`, `foo.match_1`, `foo.eq_1`: charge them to `foo`. -/
partial def owner (n : Name) : Name :=
  match n with
  | .str p s =>
    if s.startsWith "_" || s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "proof_" || s == "eq_def"
       || s == "sizeOf_spec" || s == "injEq" || s == "inj" || s == "noConfusion" || s == "noConfusionType"
       || s == "recOn" || s == "casesOn" || s == "rec" || s == "below" || s == "brecOn" || s == "binductionOn"
       || s == "ibelow" || s == "ndrec" || s == "ndrecOn" then owner p else n
  | _ => n

def walk (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := [start]
  let mut fuel := 4000000
  while fuel > 0 do
    fuel := fuel - 1
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      if (interesting env n).isNone then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        for c in ci.getUsedConstantsAsSet.toList do
          unless seen.contains c do stack := c :: stack
  return seen

def rangeLines (n : Name) : MetaM Nat := do
  match ← findDeclarationRanges? n with
  | some r => return r.range.endPos.line - r.range.pos.line + 1
  | none => return 0

def main' : MetaM Unit := do
  let env ← getEnv
  let used := walk env `TBeta.no_fixed_point_combinator
  let usedOwners : NameSet := used.toList.foldl (fun s n => s.insert (owner n)) {}
  let mut out := ""
  let mut outAll := ""
  for (n, _) in env.constants.map₁.toList do
    if n.isInternal then continue
    if let some m := interesting env n then
      if owner n != n then continue
      let l ← rangeLines n
      if l == 0 then continue
      let u := usedOwners.contains n
      let (a, b) ← match ← findDeclarationRanges? n with
        | some r => pure (r.range.pos.line, r.range.endPos.line)
        | none => pure (0, 0)
      outAll := outAll ++ s!"{m}\t{n}\t{l}\t{u}\t{a}\t{b}\n"
  -- edges between modules
  let mut edges : Std.HashMap (Name × Name) Nat := {}
  for n in used.toList do
    if let (some m, some ci) := (interesting env n, env.find? n) then
      for c in ci.getUsedConstantsAsSet.toList do
        if let some m2 := interesting env c then
          if m != m2 && used.contains c then
            edges := edges.insert (m, m2) (edges.getD (m, m2) 0 + 1)
  for ((a, b), k) in edges.toList do
    out := out ++ s!"{a}\t{b}\t{k}\n"
  IO.FS.writeFile "logs/dep_all.tsv" outAll
  IO.FS.writeFile "logs/dep_edges.tsv" out
  logInfo m!"used constants {used.size}"
  logInfo m!"done"

#eval main'
