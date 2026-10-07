# Clipped-profile Mellin responses

FIB401 continuous clipped-window templates and FIB402 conditional actual-kernel allowances, not integer-window realizations or signed H sums. Existing FIB399 scalar data are consumed; old Binet, inverse-kernel, PNT, and zero enumeration calculations are not rerun. Analytic applications not Lean verified.

Both windows have logarithmic width 1/100. The manuscript sector bound
applies throughout abs(Im(z)) < 100*pi when Re(z)>0; the sampled
frequencies below are integer parameters, not asserted zeta zero positions.

The final column is conditional on the manuscript exact-kernel bridge
and uses ell=109389; it bounds abs(ell*T_actual).

| Window | sigma | tau | Sector lower bound for abs(T) | Conditional lower bound for abs(ell*T_actual) |
| --- | --- | --- | --- | --- |
| negative | 1/2 | 0 | [0.00018704751561410956126 +/- 9.25e-24] | [2.2468998399833886e-9 +/- 4.24e-26] |
| negative | 1/2 | 14 | [6.659662558843460953e-6 +/- 3.67e-25] | [7.9998895941924968e-11 +/- 8.84e-28] |
| negative | 1/2 | 100 | [8.207379305792859134e-7 +/- 5.10e-26] | [9.859077351721788e-12 +/- 5.26e-28] |
| negative | 1/2 | 300 | [2.2051999094641543876e-8 +/- 8.96e-28] | [2.6489864393219618e-13 +/- 5.84e-30] |
| positive | 1/2 | 0 | [0.0002169785409098281719 +/- 1.95e-23] | [2.22357679157676211640e-5 +/- 4.72e-26] |
| positive | 1/2 | 14 | [7.725330433956674453e-6 +/- 3.48e-25] | [7.9168499281901180510e-7 +/- 5.17e-27] |
| positive | 1/2 | 100 | [9.520710182210621051e-7 +/- 3.31e-26] | [9.7567391280826858509e-8 +/- 2.33e-28] |
| positive | 1/2 | 300 | [2.558072248108085144e-8 +/- 5.41e-27] | [2.62148969120111104844e-9 +/- 4.06e-30] |

Closed endpoint formulas and independent Arb integrals overlap
for all ten responses, including the removable z=1 value in both windows.
The JSON stores their exact outward dyadic endpoints.

Source: [existing ratio data](robin-kernel-ratio.json).
Data: [directed responses](robin-clipped-mellin.json).
Producer: [robin_clipped_mellin.py](robin_clipped_mellin.py).

Reproduce with Python 3.13 and python-flint 0.9.0:

```sh
uv run --python 3.13 --with python-flint==0.9.0 python docs/reports/fib-robin-boundary/robin_clipped_mellin.py --source docs/reports/fib-robin-boundary/robin-kernel-ratio.json --output /tmp/robin-clipped-mellin.json --report /tmp/robin-clipped-mellin.md
```

No actual arithmetic cancellation or full Robin/RH conclusion follows.
