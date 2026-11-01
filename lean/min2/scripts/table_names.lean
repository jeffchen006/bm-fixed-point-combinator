import TBeta.Main
import TBeta.Control
import TBeta.Corollaries
import TBeta.Restate
import Lean
open Lean
/-! Checks that each name in `TABLE.md` exists. It does not compare types. Run with `lake env lean scripts/table_names.lean`. -/
def tableNames : List String := ["Alive", "Alive.conv", "Alive.peel", "Alive.peelN", "B_run", "Bd", "Bd_append", "Bd_pop", "Bd_up", "Ch", "Ch.d", "Ch.t", "Dy", "E", "EL", "G", "G.cx", "G.hx", "G.rd", "G.redsH", "G.shift", "G.step", "G.stepH", "G.sub", "G.transB", "G.transD", "HR", "HR.of_reds", "HasX", "Hk", "I_run", "Int", "Int.vh", "J", "J_S", "J_conv", "J_mono", "J_shift", "J_step", "J_subst", "J_xp", "Kd", "LastX", "LastX.pop", "LeanJudge.conv_B", "LeanJudge.conv_I", "LeanJudge.conv_M", "Lt", "MK", "M_run", "Mv", "NS", "OK", "Rep", "Rep.BU", "Rep.BUV", "Run", "S", "S_append", "S_lift", "S_plug", "St", "St.facts", "St.init", "St.next", "St.shape", "Stuck", "VH", "VH.reds", "W", "W.cases'", "W.term", "Walk", "Y_subst", "a0", "a0_F", "aT", "abstract_at", "alive_of_fix", "appsT", "bodyOK", "bodyOK_shift", "bodyOK_subst", "bp", "bz", "church_rosser", "cl_term", "conv_eta_exp", "conv_xp", "coreW", "coreW_not_fix", "coreW_state", "dg", "dg_pop", "dg_up", "eta_run", "exists_Bd", "exists_down", "fact_dist", "first_arg", "hasX_of_up", "hat", "hat_app", "hat_up", "hx", "int_ns", "int_subst", "iterApp", "iterx", "iterx_eq", "lam_stuck", "legal", "letter", "level_of_bz", "lift", "list_rule", "lt", "lt_red", "mono", "mono_lt", "no_fix_var", "no_fix_x", "no_fix_xr", "no_fixed_point_combinator", "no_weak_xr", "not_alive_hat", "not_alive_lam", "not_alive_two", "not_alive_x", "ns_det", "ns_subst", "nx", "ok_of", "over_BM", "par_factor", "par_run_vh", "partA", "plug", "plug_red", "plug_up_app", "pop", "pop1", "pop_conv", "rd", "reds_no_eta", "rsplit", "run", "run_B", "run_I", "run_M", "run_conv", "run_prefix", "run_step", "run_subst", "shape_of_alive", "sigma_zero_control", "split_where", "start", "state_not_fix", "step_no_eta", "step_not_var", "step_split", "theorem_1", "theorem_1_BM", "toL", "toW", "toW_term", "two_letters", "two_walk", "up", "up1", "upK", "val", "walk_pos", "walk_zero", "wconv_conv", "xc", "xp", "xp_add"]
def prefixes : List Name := [`TBeta, `TBeta.N, `TBeta.G2, `TBeta.Restate, `PartA, `LeanJudge, Name.anonymous]
def strToName (s : String) : Name := (s.splitOn ".").foldl (fun n p => Name.mkStr n p) Name.anonymous
run_cmd do
  let env ← getEnv
  let mut bad := #[]
  for n in tableNames do
    let found := prefixes.filter fun p => env.contains (p ++ strToName n)
    if found.isEmpty then bad := bad.push n
  logInfo m!"{tableNames.length} names, missing: {bad}"
