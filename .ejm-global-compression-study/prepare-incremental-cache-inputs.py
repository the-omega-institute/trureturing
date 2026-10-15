"""Extract the actual cache mirrors and operation tables for native replay.

This is input preparation, never a kernel receipt. No replacement action or
source table is introduced into Lean; all finite maps are read from owners.
"""
import hashlib
import json
import pathlib
import re

wt = pathlib.Path(__file__).resolve().parent.parent
source = wt / 'D5/S3/Quantum/Entanglement/EJM'
cp = pathlib.Path('/Users/macstudio/omega/.formalization-goal-01a12631/checkpoints/ejm-mdd-global/existing-cover-original-suffix-alignment-20261014')
out = cp / 'original-source-identity-stream'
cache = (source/'EJMLocalCacheData.lean').read_text()
certificate = (source/'EJMCertificateData.lean').read_text()
data = (source/'EJMPartialBoundData.lean').read_text()

def section(text, name):
    result = text.split('def '+name+' :',1)[1]
    return result.split('\n\n',1)[0]

def matrix(text, name, rows, cols):
    result = [[int(x) for x in r.split(',')] for r in
        re.findall(r'!\[([0-9,]+)\]', section(text,name))]
    assert len(result)==rows and all(len(r)==cols for r in result), name
    return result

outcomes = matrix(data,'outcome',24,4)
omul = matrix(cache,'outcomeMul',24,24)
inverse = [int(x) for x in re.search(r'def coordinateInverse.*?!\[([0-9,]+)\]',cache).group(1).split(',')]
assert len(inverse)==12
for t in range(24):
    for s in range(24):
        assert outcomes[omul[t][s]] == [outcomes[t][outcomes[s][a]] for a in range(4)]

lines = ['EJM_ACTUAL_INCREMENTAL_CACHE_V1']
lines.extend(' '.join(map(str,r)) for r in outcomes)
lines.extend(' '.join(map(str,r)) for r in omul)
lines.append(' '.join(map(str,inverse)))
records=[]
for label,n,count in [('Triangle',10,41294),('Singleton',9,8689)]:
    text=(source/f'EJM{label}CacheData.lean').read_text()
    literals=re.findall(r'\(\.node (\d+) ⟨(\d+), \((-?\d+)\), (0x[0-9a-f]+), (0x[0-9a-f]+)⟩',text)
    rows={int(j):(int(key),int(lower),int(slots,16),int(edges,16))
        for j,key,lower,slots,edges in literals}
    assert len(literals)==count and sorted(rows)==list(range(count))
    # Parse the real part graph and prove that MirrorTree.get reaches exactly
    # these rows under its equality/less-than search semantics.
    matches=list(re.finditer(r'private def (mirrorTreePart\d+)\s*:\s*MirrorTree\s*:=',text))
    parts={}
    for k,match in enumerate(matches):
        rhs=text[match.end():matches[k+1].start() if k+1<len(matches) else len(text)]
        rhs=rhs.split('@[noinline]')[0].split('\ndef ')[0]
        tokens=re.findall(r'\.node|\.empty|0x[0-9a-f]+|-?\d+|[A-Za-z]\w*|[()⟨⟩,]',rhs)
        at=0
        def parse():
            global at
            token=tokens[at];at+=1
            if token=='(':
                value=parse();assert tokens[at]==')';at+=1;return value
            if token=='.empty':return None
            if token!='.node':return parts[token]
            index=int(tokens[at]);at+=1
            assert tokens[at]=='⟨';at+=1
            fields=[]
            for field in range(4):
                paren=tokens[at]=='('
                if paren:at+=1
                fields.append(int(tokens[at],0));at+=1
                if paren:assert tokens[at]==')';at+=1
                assert tokens[at]==(',' if field<3 else '⟩');at+=1
            assert tuple(fields)==rows[index]
            left,right=parse(),parse()
            assert left is None or left[1]<index
            assert right is None or index<right[0]
            return (left[0] if left else index,right[1] if right else index,
                1+(left[2] if left else 0)+(right[2] if right else 0))
        parts[match.group(1)]=parse();assert at==len(tokens)
    final=re.search(r'def mirrorTree\s*:\s*MirrorTree\s*:=\s*(\w+)',text)
    assert parts[final.group(1)]==(0,count-1,count)
    lower_label=label.lower()
    perms=matrix(certificate,lower_label+'Perm',12,n)
    cmul=matrix(certificate,lower_label+'Mul',12,12)
    for s in range(12):
        assert [perms[s][perms[inverse[s]][i]] for i in range(n)]==list(range(n))
        for t in range(12):
            assert perms[cmul[s][t]]==[perms[s][perms[t][i]] for i in range(n)]
    incidence=[]
    for row in re.findall(r'!\[([^\[\]]+)\]',section(cache,lower_label+'Incidence')):
        incidence.append([-1 if x.strip()=='none' else int(x.strip().split()[1]) for x in row.split(',')])
    assert len(incidence)==20 and all(len(r)==16 for r in incidence)
    lines.append(f'{n} {count}')
    for table in [perms,cmul,incidence]:
        lines.extend(' '.join(map(str,r)) for r in table)
    unknown_edges=0
    for j in range(count):
        key,lower,slots,edges=rows[j]
        words=[]
        for i in range(n):
            for a in range(4):
                word=edges>>(25*(4*(slots>>(4*i)&15)+a))&((1<<25)-1)
                words.append(word)
                if key//5**i%5==4:
                    assert (word&65535)<count and (word>>16)%512<288
                    unknown_edges+=1
        lines.append(' '.join(map(str,[key,lower]+words)))
    assert rows[count-1][0]==5**n-1
    records.append(dict(block=label,rows=count,unknown_coordinate_value_edges=unknown_edges,
        actual_mirror_BST_checked=True,actual_composition_checked=True))
payload='\n'.join(lines)+'\n'
(out/'actual-incremental-cache.txt').write_text(payload)
paths=[source/name for name in ['EJMLocalCacheData.lean','EJMCertificateData.lean',
    'EJMPartialBoundData.lean','EJMTriangleCacheData.lean','EJMSingletonCacheData.lean','EJMCacheState.lean']]
record=dict(status='actual_incremental_cache_inputs_extracted_not_kernel',kernel_accepted=False,
    blocks=records,extracted_sha256=hashlib.sha256(payload.encode()).hexdigest(),
    source_files={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
(out/'actual-incremental-cache-inputs.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
