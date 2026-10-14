from pathlib import Path
import subprocess, json, difflib
rel='D5/S3/Zeros/Jensen/OriginalPrimalTailResponse.lean'
old=subprocess.check_output(['git','show','HEAD:'+rel],text=True)
new=Path(rel).read_text()

def lex(s):
    out=[]; comments=[]; strings=[]; i=0; n=len(s)
    while i<n:
        c=s[i]
        if c.isspace(): i+=1; continue
        if s.startswith('--',i):
            j=s.find('\n',i)
            if j<0:j=n
            tok=s[i:j]; out.append(('comment',tok)); comments.append(tok); i=j; continue
        if s.startswith('/-',i):
            start=i; depth=1; i+=2
            while i<n and depth:
                if s.startswith('/-',i): depth+=1; i+=2
                elif s.startswith('-/',i): depth-=1; i+=2
                else:i+=1
            tok=s[start:i]; out.append(('comment',tok)); comments.append(tok); continue
        if c=='"':
            start=i; i+=1; esc=False
            while i<n:
                if esc: esc=False; i+=1
                elif s[i]=='\\': esc=True; i+=1
                elif s[i]=='"': i+=1; break
                else:i+=1
            tok=s[start:i]; out.append(('string',tok)); strings.append(tok); continue
        # Lean identifiers (including unicode letters/numbers and primes).
        if c=='_' or c.isalnum() or (ord(c)>127 and (c.isidentifier() or c.isalnum())):
            start=i; i+=1
            while i<n:
                d=s[i]
                if d=='_' or d.isalnum() or d=="'" or (ord(d)>127 and (d.isidentifier() or d.isalnum())):
                    i+=1
                else: break
            out.append(('word',s[start:i])); continue
        # Compare punctuation one codepoint at a time; comments/strings above
        # remain exact opaque tokens.
        out.append(('punct',c)); i+=1
    return out,comments,strings

ot,oc,os=lex(old); nt,nc,ns=lex(new)
# Physical and blank-line readings.
def stats(s):
    ls=s.splitlines()
    return {'physical_lines':len(ls),'blank_lines':sum(not x.strip() for x in ls)}
res={
 'path':rel,
 'old':stats(old), 'new':stats(new),
 'old_token_count':len(ot), 'new_token_count':len(nt),
 'token_sequence_equal':ot==nt,
 'comments_equal':oc==nc, 'strings_equal':os==ns,
 'comment_count':len(oc), 'string_count':len(os),
 'old_sha256':__import__('hashlib').sha256(old.encode()).hexdigest(),
 'new_sha256':__import__('hashlib').sha256(new.encode()).hexdigest(),
}
if ot!=nt:
    for idx,(a,b) in enumerate(zip(ot,nt)):
        if a!=b:
            res['first_token_mismatch']={'index':idx,'old':a,'new':b}; break
    if len(ot)!=len(nt): res['length_mismatch']=(len(ot),len(nt))
# Count actual changed physical lines for the report, without treating pure
# whitespace as a token change.
res['unified_diff_lines']=sum(1 for l in difflib.unified_diff(old.splitlines(),new.splitlines(),lineterm='') if l.startswith(('+','-')) and not l.startswith(('+++','---')))
print(json.dumps(res,ensure_ascii=False,sort_keys=True,indent=2))
