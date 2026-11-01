#!/usr/bin/env python3
"""Per module: declarations and lines used by the final theorem."""
import collections
d=collections.defaultdict(lambda:[0,0,0,0]); un=collections.defaultdict(list); us=collections.defaultdict(list)
for line in open('logs/dep_all.tsv'):
    m,n,l,u=line.rstrip('\n').split('\t')[:4]; l=int(l); u=u=='true'
    d[m][0]+=1; d[m][1]+=l
    if u: d[m][2]+=1; d[m][3]+=l; us[m].append((l,n))
    else: un[m].append((l,n))
T=[0,0,0,0]
print("module\tdecls\tlines\tused decls\tused lines")
for m in sorted(d):
    print(m,*d[m],sep='\t')
    for i in range(4): T[i]+=d[m][i]
print('TOTAL',*T,sep='\t')
print("\nlargest used")
for m in sorted(us):
    print(m,', '.join(f"{n.split('.')[-1]} {l}" for l,n in sorted(us[m],reverse=True)[:9]))
print("\nedges")
for line in sorted(open('logs/dep_edges.tsv')): print(line.rstrip())
