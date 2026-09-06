#!/usr/bin/env python3
"""Insert the three base-brief blocks (provenance / imports / public surface) taken from briefs/impl-op-w1-ppn.md into any brief lacking them. usage: add_base_blocks.py FILE..."""
import sys,pathlib,re
base=pathlib.Path('briefs/impl-op-w1-ppn.md').read_text()
blocks=[]
for key in ['**Public surface is deliberate.**','**Imports are minimal','**Provenance is typed']:
    i=base.find(key); assert i>=0,key; j=base.find('\n\n',i); blocks.append(base[i:j+2])
for f in sys.argv[1:]:
    p=pathlib.Path(f); t=p.read_text(); added=0
    i=t.find('## Steps'); assert i>=0,f; j=t.find('\n',i)+1
    for b in blocks:
        if b[:30] not in t: t=t[:j]+'\n'+b+t[j:]; added+=1
    p.write_text(t); print(f,'blocks added:',added)
