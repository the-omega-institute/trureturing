# A finite support-dependent query exceeds the factorized envelope

Keep exactly [report548](548-rainbow-transport-forces-a-next-row-saving.md)'s 192-original N=E=4 prefix and its actual
unnormalized transported measure lambda11. No original phase, kernel,
or normalization is changed.

Define the fixed coordinate cylinders

    T5,1=[4]_5, T5,a=[14]_(5^a) for a>=2;
    D5,a=[3]_(5^a) for a>=1;
    T7,1=[5]_7, T7,b=[19]_(7^b) for b>=2;
    D7,b=[6]_(7^b) for b>=1.

For each(a,b,c) in{0,1,2,3}^3 choose one CRT cylinder Q_(a,b,c)
of numerical modulus5^a7^b11^c. Absent coordinates impose no condition.
For positive exponents, its phases are:

* a>0,b=0: use T5,a;
* a=0,b>0: use D7,b;
* a>0,b>0,c=0: use D5,a and D7,b;
* a>0,b>0,c>0: use D5,a and T7,b;
* c>0: always use[9]_(11^c).

The (a,b,c)=(0,0,0) term is the unit old cofactor, not an original modulus-one class. These are64 different numerical
labels, each with one globally fixed phase. The [query data](../../frontier/cover-geometry/support_dependent_query_boundary.json) include all 64
integer CRT residues and verify every coordinate projection.

Let L=sum Q_(a,b,c). Its exact hinge under the unchanged actual law is

    integral (L-2)_+ dlambda11
      =289905891459395808502/1661652350530156359375
      =0.1744684388204911....

It exceeds report548's factorized envelope H13 by

    46095389141128354033/79759312825447505250000 >0.

This is a finite fixed-query counterexample to EXTENDING that envelope
to these support-dependent phases. It does not contradict548's stated
factorized theorem. It is not an actual13-row loss construction or a
counterexample to NC4.

## Exact integral

Write X_p,T and X_p,D for the numbers of positive cylinders among the
three specified coordinate depths. At old11 exponent zero the load is

    M0=1+X5,T+X7,D+X5,D*X7,D.

At each positive old11 exponent it is

    M1=1+X5,T+X7,D+X5,D*X7,T.

Thus L=M0+M1*V, where V is the sum of the three nested[9]_(11^c)
indicators. At K<10 the whole11-root9 is allowed. Put

    r=11^-4,
    g_K=1-(K/10)(1-r),
    h_K=min(5/3,1/g_K), s_K=h_K*g_K,
    v3=(1-11^-3)/10.

For each fixed old point the exact11 integral is

    s_K*(M0-2)_+ + h_K*v3*M1 - (h_K/11)*1_(M0=1).

Indeed M0>=2 makes the hinge affine in V. When M0=1, M1>=1 and
(M1*V-1)_+=M1*V-1_(V>0); the surviving root9 has mass1/11.
At K=10 that root is forbidden, so V=0 and the integral is exactly
s_10*(M0-2)_+.

Two independent finite evaluations agree. One groups the joint old
state with both T/D counts and uses their exact truncated first
moments. The identity(M0-2)_+=M0-2+1_(M0=1) makes this exact even
when a complete-tail atom is represented by mass and first moment.
The second partitions the literal finite p-adic prefixes:73 leaves
at5 and109 leaves at7, aggregating to20 retained groups per prime.
It removes the actual mixed product eta and evaluates the integer
counts directly. It does not use the first method's tail moments.
Neither method enumerates a full CRT period.

## The complete256-layout search has a different boundary

For each of the two old11-support classes, independently choose the
single5 chain, single7 chain and the pair of chains at joint57 support.
This gives16 choices per class and256 total. All positive old11 phases
remain the same fixed nested9 chain. The complete query-height optimum
within THIS class is uniquely

    A=T/D/DD, B=T/D/DT,
    Hmax=23482695373494078575017/132932188042412508750000.

It exceeds H13, but is below the13-only closure target

    F13-4*c0/(257/51-2)
      =1219319567805006647183/6737898677007930432000

by3342407997448099804533816395037/
775018947074607374745165560000000, about0.00431267908.

For the maximizing template the exact complete-minus-finite difference is

    Hmax-Hfinite64
      =290224056742413894857/132932188042412508750000.

Subtracting this exact truncation difference from Hmax-H13 leaves the
strict finite margin displayed above. The finite witness therefore does
not rely on an unquantified convergence argument or a floating-point
tail cutoff; its integral is evaluated exactly at the stated64 labels.

Therefore this256-layout family does not reach that target. This is
not an upper bound for arbitrary old11 phases, arbitrary nested
layouts, arbitrary support-dependent queries, or actual13 losses.

## Verification and the remaining unrestricted task

The [standalone query program](../../frontier/cover-geometry/support_dependent_query_boundary.py)
and its [data](../../frontier/cover-geometry/support_dependent_query_boundary.json)
pass 27 named exact checks, including 256 direct-versus-separated integrals,
the 64 explicit CRT phases, and the finite prefix evaluation. Every complete
tail is summed with exact mass and first moment; the lower witness itself
uses only the stated finite labels.

A separate [finite-box program](../../frontier/cover-geometry/support_dependent_query_direct.py)
and its [data](../../frontier/cover-geometry/support_dependent_query_direct.json)
construct all 192 original boxes and 64 query boxes. The three literal
prefix partitions have 73, 109 and 61 leaves at 5, 7 and 11. Directly removing
the actual forbidden union and applying the actual capped 11-kernel over
109857 joint survivor cells gives the same finite hinge. This evaluation
uses neither the first program's atom formulas nor an infinite tail. It
also gives the actual unnormalized mass

    lambda11(1)=121611906311383/565194987328125.

Both programs use only the Python standard library, import no project
producer or prior data, and keep failure checks active under optimization.
No full original-period enumeration or Lean build was run.
The result SHA256 values, in the same order, are
`88b610967e85493bfbae034ebba5cddc7320601f8bbcb9834396528f34a3cf37`
and `ab79374a08016d9438a2dcf1a016b07212bb1323ae16ac26bf46ec2c86fbe5bf`.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/support_dependent_query_boundary.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/support_dependent_query_direct.py
```

The result excludes direct reuse of the factorized constant once phases
can depend on old support. It neither bounds all such queries nor supplies
an actual 13-row loss. A common quantitative law for arbitrary original
families, with every original phase fixed globally, remains unresolved.

[The seven-label uniform bound](551-seven-shallow-labels-control-every-rainbow-continuation.md) controls every fixed support-dependent query after the same prefix by0.1793490612..., above this counterexample but below the13-only closure threshold. It removes the continuation restrictions while retaining the fixed original prefix.
