from pathlib import Path
import subprocess
src=Path('D5/S3/Zeros/Jensen/OriginalPrimalTailResponse.lean')
orig=subprocess.check_output(['git','show','HEAD:'+str(src)],text=True).splitlines()
# Drop blank lines, retaining a spacer before doc comments for readability.
lines=[]
for i,l in enumerate(orig):
    if l.strip():
        lines.append(l)
stop_starts=(
    'private theorem','theorem ','private def','def ','import ','set_option ',
    'namespace ','end ','#print','noncomputable','open ','section ','variable ',
    'example ','let ','have ','rw ','exact ','apply ','simpa ','simp ','norm_num',
    'nlinarith','ring','rfl','constructor','intro ','refine ','change ','dsimp ',
    'unfold ','induction ','obtain ','clear ','filter_upwards','convert!','first ',
    'calc','linear_combination','omega','push_cast','field_simp','congr','fun_prop',
    'positivity','aesop','·','| ')
tactic_starts=stop_starts
ops=(':=',':','=>','from','=', '≤','≥','<','>','+','-','*','/','∧','∨','→','←','(', '[','{',',','⟨')
def indent(s): return len(s)-len(s.lstrip())
def depth(s):
    # Delimiter depth outside strings/comments; source uses block comments only
    # for the header and doc comments, which are handled conservatively here.
    d=0; ins=False; esc=False; i=0
    while i<len(s):
        c=s[i]
        if ins:
            if esc: esc=False
            elif c=='\\': esc=True
            elif c=='"': ins=False
            i+=1; continue
        if c=='"': ins=True; i+=1; continue
        if s.startswith('/-',i):
            j=s.find('-/',i+2)
            if j<0: break
            i=j+2; continue
        if c in '([{': d+=1
        elif c in ')]}': d-=1
        i+=1
    return d
def can_join(a,b,after=None):
    sa,sb=a.strip(),b.strip()
    if not sa or not sb or sa.startswith('--') or sb.startswith('--'):
        return False
    if sb.startswith('/-'):
        return False
    # Keep tactic block indentation. A `by` body may move inline only when
    # it is the sole tactic line before the surrounding block dedents.
    if sa.endswith('by'):
        if sb.startswith(('·','| ')):
            return False
        if after is not None and (not after.strip() or indent(after) >= indent(b)):
            return False
        return True
    if sb.startswith(tactic_starts):
        return False
    if sb.startswith((')',']','}',',','∧','∨','→')):
        return True
    if sa.endswith(ops):
        return True
    # A still-open parenthesis/bracket is an unambiguous term continuation.
    # Exclude tactic starts above so nested tactic blocks retain their layout.
    if depth(a)>0 and not sa.endswith('by'):
        return True
    if sa.startswith('open private') and indent(b)>indent(a):
        return True
    if sa=='calc' and sb.startswith('_'):
        return True
    return False
out=[]
i=0
while i<len(lines):
    if i+1<len(lines) and can_join(lines[i],lines[i+1],lines[i+2] if i+2<len(lines) else None):
        out.append(lines[i].rstrip()+' '+lines[i+1].strip()); i+=2
    else:
        out.append(lines[i]); i+=1
src.write_text('\n'.join(out)+'\n')
