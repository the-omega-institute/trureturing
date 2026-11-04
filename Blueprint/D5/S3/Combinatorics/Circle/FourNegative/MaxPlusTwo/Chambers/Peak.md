# The exact first reserve at T=2Z

## Abstract

Adjacent peak with advanced V bits

Write Z=2P with R>=4 and P>=2, C=2RZ+R+1, A=2RZ^2+C, e=4ZC and Delta=8A-2e. The internal polynomial inequalities prove Delta>0, e>3A, Delta<e-A and e-3A<=Delta(P-1). For n=ceilpos(e-3A,Delta), peak_advance_bounds proves 1<=n<=P-1 and e<=A(8n+3)-2en<=2e-A. The same capacity gives 8n+3<=4Z-5. Thus the advanced V mask n and the U reserve 8n+3 fit their physical capacities. This handles the adjacent-ratio first seam without a uniform one-reserve selector. The other seams and chambers retain their full unbounded proof obligations.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Arithmetic](Arithmetic.md)
