from pathlib import Path
p=Path('D5/S3/Zeros/Jensen/OriginalPrimalTailResponse.lean')
orig=p.read_text().splitlines()
lines=[l for l in orig if l.strip()]
stop_starts=('private theorem','theorem ','private def','def ','import ','set_option ','namespace ','end ','#print','noncomputable','open ','section ','variable ','example ','let ','have ','rw ','exact ','apply ','simpa ','simp ','norm_num','nlinarith','ring','rfl','constructor','intro ','refine ','change ','dsimp ','unfold ','induction ','obtain ','clear ','filter_upwards','convert!','first ','calc','linear_combination','omega','push_cast','field_simp','congr','fun_prop','positivity','aesop','·','| ')
ops=(':=','=', '≤','≥','<','>','+','-','*','/','∧','∨','→','←','(', '[','{',',','⟨')
def indent(s): return len(s)-len(s.lstrip())
def can(a,b):
    sa=a.strip(); sb=b.strip()
    if not sa or not sb:return False
    if sa.startswith('--') or sb.startswith('--'): return False
    ia,ib=indent(a),indent(b)
    # by starts a tactic sequence; join one first tactic even if keyword
    if sa.endswith('by') and not sb.startswith(('·','| ')):
        return True
    if sb.startswith(stop_starts): return False
    if sa.endswith(ops): return True
    if sb.startswith((')',']','}',',','∧','∨','→','+','-','*','/')): return True
    if sa.startswith('open private') and ib>ia: return True
    if sa=='calc' and sb.startswith('_'): return True
    return False
out=[]
i=0
while i<len(lines):
    a=lines[i]
    if i+1<len(lines) and can(a,lines[i+1]):
        out.append(a.rstrip()+' '+lines[i+1].strip()); i+=2
    else: out.append(a); i+=1
print('orig nonblank',len(lines),'out',len(out),'joins',len(lines)-len(out))
for i,l in enumerate(out,1): print(f'{i:4} {l}')
