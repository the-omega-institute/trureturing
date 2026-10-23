# Self-calibrating acquisition resources XXIV: an eight-active matched family and the restriction obstruction

## 375. The eight-active profiles

Retain the source, carrier, marks, one-seed hard-two interfaces, complete tables, independent event rows, and literal affine anchor of [XXIII 368.1–368.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXIII.md). In particular, a complete stopped pair has cells \(0,10,11\), a complete preselected pair has cells \(00,01,10,11\), every cell of one schedule has its owning mass, and the rows (A,C,P,T) are imposed independently. For \(L=8\), write

$$
 b(h)=\left(h,{34\over64},{34\over64},{29\over64},{27\over64},
                 {25\over64},{22\over64},{20\over64}
\right),qquad
 {17\over32}\le h\le {43\over64},
$$

and put

$$
 c={2867\over11856}.
$$

The admissible infinite profiles are the entire sequences

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad a_i\longrightarrow0,\qquad
(a_1,\ldots ,a_8)=b(h),\qquad a_9\le c.
$$

The inequality \(a_9\le c<a_8\) keeps the active prefix equal to eight. Every finite Boolean word on these eight coordinates, including words with several zeros, has an actual source in the original \(X\). Thus a finite table satisfying the rows is transported to an original acquisition by the common-seed construction of [XXIII 368.2] and the positive-tail identity of [XXIII 373.1].

## 376. One allocation for both resource classes

For a vector \(v\in\mathbb R^9\), write \(v/47424\) for coordinatewise division by (47424). In the following table the entries are integer vectors in label order (0,1,\ldots ,8), and the three displayed cells are in stopped order (0,10,11). The first column is the schedule and the second is its owning mass, also with denominator (47424).

$$
\begin{array}{c|c|c|c|c}
S&m_S&X^0&X^{10}&X^{11}\\ \hline
12&11363&(0,11363,0,0,0,0,0,0,0)&(0,0,11363,0,0,0,0,0,0)&(5698,0,0,2776,2889,0,0,0,0)\\
13&5475&(463,5012,0,0,0,0,0,0,0)&(0,0,0,5475,0,0,0,0,0)&(5475,0,0,0,0,0,0,0,0)\\
14&1657&(0,1657,0,0,0,0,0,0,0)&(0,0,0,0,1657,0,0,0,0)&(1657,0,0,0,0,0,0,0,0)\\
15&1434&(0,1434,0,0,0,0,0,0,0)&(0,0,0,0,0,1434,0,0,0)&(1434,0,0,0,0,0,0,0,0)\\
16&929&(0,929,0,0,0,0,0,0,0)&(0,0,0,0,0,0,929,0,0)&(929,0,0,0,0,0,0,0,0)\\
23&5475&(4769,0,706,0,0,0,0,0,0)&(0,0,0,5475,0,0,0,0,0)&(5475,0,0,0,0,0,0,0,0)\\
24&1657&(0,0,1657,0,0,0,0,0,0)&(0,0,0,0,1657,0,0,0,0)&(1657,0,0,0,0,0,0,0,0)\\
25&1434&(1434,0,0,0,0,0,0,0,0)&(0,0,0,0,0,1434,0,0,0)&(1434,0,0,0,0,0,0,0,0)\\
26&929&(929,0,0,0,0,0,0,0,0)&(0,0,0,0,0,0,929,0,0)&(929,0,0,0,0,0,0,0,0)\\
34&3818&(3818,0,0,0,0,0,0,0,0)&(0,0,0,0,3818,0,0,0,0)&(1973,0,0,0,0,1725,0,120,0)\\
35&1973&(1973,0,0,0,0,0,0,0,0)&(0,0,0,0,0,1973,0,0,0)&(1973,0,0,0,0,0,0,0,0)\\
36&1468&(1468,0,0,0,0,0,0,0,0)&(0,0,0,0,0,0,1468,0,0)&(1468,0,0,0,0,0,0,0,0)\\
37&189&(189,0,0,0,0,0,0,0,0)&(0,0,0,0,0,0,0,189,0)&(189,0,0,0,0,0,0,0,0)\\
45&1973&(1973,0,0,0,0,0,0,0,0)&(0,0,0,0,0,1973,0,0,0)&(1973,0,0,0,0,0,0,0,0)\\
46&1468&(1468,0,0,0,0,0,0,0,0)&(0,0,0,0,0,0,1468,0,0)&(1468,0,0,0,0,0,0,0,0)\\
47&189&(189,0,0,0,0,0,0,0,0)&(0,0,0,0,0,0,0,189,0)&(189,0,0,0,0,0,0,0,0)\\
56&2263&(2263,0,0,0,0,0,0,0,0)&(0,0,0,0,0,0,2263,0,0)&(1468,0,0,0,0,0,0,795,0)\\
57&1144&(1144,0,0,0,0,0,0,0,0)&(0,0,0,0,0,0,0,1144,0)&(189,0,0,0,0,0,0,0,955)\\
67&2397&(2397,0,0,0,0,0,0,0,0)&(0,0,0,0,0,0,0,2397,0)&(189,0,0,0,0,0,0,0,2208)\\
78&189&(189,0,0,0,0,0,0,0,0)&(0,0,0,0,0,0,0,0,189)&(189,0,0,0,0,0,0,0,0)
\end{array}
$$

The twenty masses sum to (47424/47424=1), and every cell in a row sums to its displayed mass. Let (p_w) be the sum of the cell selected by (w) in every row. For (\mathcal O_2), this is the stopped table. For (\mathcal N_2), replace the first cell of every row by two equal cells (X^{00}=X^{01}=X^0); this is a complete preselected table with exactly the same word law. The interval-seed realization fixes all these cells before replies. Thus the same twenty schedule masses give one lawful (N) allocation and one lawful stopped (O) allocation.

## 377. Exact cap calculation

For \(n=1,\ldots ,8\), let \(A_n,C_n,P_n\) be respectively the minima over all words with first zero (n) of \(p_w(0),p_w(n),p_w(0)+p_w(n)\). Adding the displayed vectors gives the following exact table. A word in the last column attains all three entries in its row except where a separate word is shown; the listed words also show that the minima are attained, not merely bounded.

$$
\begin{array}{c|c|c|c|c}
 n&A_n&C_n&P_n&\text{attaining words }(A,C,P)\\ \hline
1&21/64&20395/47424&8989/11856&(00110000,00000000,00110000)\\
2&15/32&6863/23712&8989/11856&(10001000,10000000,10001000)\\
3&15/32&6863/23712&8989/11856&(11000100,11000000,11000100)\\
4&8757/15808&10021/47424&9073/11856&(11100000,11100000,11100000)\\
5&3491/5928&8539/47424&36467/47424&(11110000,11110000,11110000)\\
6&10445/15808&7057/47424&4799/5928&(11111000,11111000,11111000)\\
7&550/741&2417/23712&20017/23712&(11111100,11111100,11111100)\\
8&35767/47424&419/5928&39119/47424&(11111110,11111110,11111110)
\end{array}
$$

The calculation is finite and direct: for a word (w), choose (0,10,11) in each of the twenty rows according to its two bits, add the nine coordinates, and then group by the first zero. The table includes all \(2^8-1\) zero words and every one of the nine labels; in particular, multiple-zero words are not discarded. The positive word is

$$
 p_{1^8}=\frac1{47424}(35956,0,0,2776,2889,1725,0,915,3163),
 \qquad p_{1^8}(0)={8989\over11856}=1-c.
$$

At either endpoint \(h=17/32\) or \(h=43/64\), the literal demands (1-b_n-c, b_n-c, 1-c) are no larger than the corresponding entries of the table. For \(n=1\), the largest base demand is (1-17/32-c=5381/23712<21/64), while at \(h=43/64\) the correct demand is (43/64-c=20395/47424). For \(n=2,\ldots ,8\), the correct rows are equalities at (n=2,3,4,5,6,7,8) after the displayed rational substitutions, and every base and union row has nonnegative slack. Since each demand is affine in \(h\), the same allocation satisfies all rows for every (h) in the closed interval. For a source with first zero \(n>8\), [XXIII 373.1] gives

$$
\operatorname{TV}(p_{1^8},\lambda_x^a)=\max\{1-p_{1^8}(0),a_n\}=c.
$$

Consequently the allocation has selected-law error at most (c), and the word attaining a zero row in the table or the positive tail gives equality.

## 378. A zero-cost lower certificate with literal affine mass

Define the full score \(Y\) by the following nonzero rows; the type \((P,C,T)\) has the meaning of [XXIII 368.4]. Every unlisted row, including every \(A\)-row and the positive row unless listed, has weight zero.

$$
\begin{array}{c|c|r@{\qquad}c|c|r}
P&00110000&26&P&01001000&22\\
P&01001010&4&P&01001100&7\\
P&01001101&4&P&01010100&35\\
P&01011000&30&P&01100000&12\\
P&01100010&40&P&01100100&13\\
P&01110000&4&P&10001010&6\\
P&10001100&19&P&10010000&14\\
P&10010010&40&P&10010100&13\\
P&10011001&10&P&10100000&2\\
P&10100100&35&C&10110000&25\\
P&10101000&40&&&\\
C&10110010&1&C&11000000&62\\
P&11000100&6&P&11000110&22\\
P&11001010&12&C&11010010&40\\
C&11011100&26&C&11100000&128\\
C&11100100&2&C&11101011&10\\
C&11101100&28&C&11110000&138\\
C&11110100&20&C&11111000&140\\
C&11111001&10&C&11111100&150\\
C&11111101&8&C&11111110&150\\
T&11111111&128&&&
\end{array}
$$

Direct accumulation of the rows gives

$$
 C_0=544,\qquad
 \beta=(0,26,128,168,158,150,158,150),qquad K=1482,
$$

and hence \(W_Y=C_0+\beta _1+\beta _2=570\). For completeness, the cell-maximization rule is

$$
 H_{S,c}=\max_{0\le z\le8}
       \sum_{w:\,\operatorname{cell}_S(w)=c}f_Y(w,z).
$$

Summing these maxima over the cells gives 544 for the empty schedule and every singleton. For pairs, the complete list of sums is

$$
\begin{array}{c|rrrrrrrrrrrrrr}
S&12&13&14&15&16&17&18&23&24&25&26&27&28&34\\ \hline
N&570&570&570&570&570&563&544&570&570&570&570&570&544&570\\
O&570&570&570&570&570&563&544&570&570&570&570&569&544&570
\end{array}
$$

$$
\begin{array}{c|rrrrrrrrrrrrrr}
S&35&36&37&38&45&46&47&48&56&57&58&67&68&78\\ \hline
N&570&570&570&544&570&570&570&550&570&570&554&570&544&570\\
O&570&570&570&544&570&570&570&544&570&570&554&570&544&570
\end{array}
$$

These numbers are obtained by the displayed finite sums, with all nine labels retained in each maximum. Thus \(B_N(Y)=B_O(Y)=570=W_Y\), so \(\Delta_N(Y)=\Delta_O(Y)=0\). The value \(570\) is attained, for example, by schedule \(12\) in both catalogs.

Let p be any complete allocation of mass M satisfying the literal affine rows at \((b,e)\). The common-mass bound of [XXIII 368.3–368.4] and \(\Delta_C(Y)=0\) give, for \(C=N,O\),

$$
 Y\cdot(z(p)-Mr)\le M\Delta_C(Y)=0.
$$

Since \(Y\cdot(d(b,e)-r)=F_{Q(Y)}(b,e)\), this is the literal, unnormalised implication

$$
 26b_2+128b_3+168b_4+158b_5+150b_6+158b_7+150b_8
       \le 26+1482e. \tag{378.1}
$$

The ((M-1)570) term has cancelled against \(Y\cdot Mr\); no division by M and no change of profile has been made. At \(b=b(h)\), the left side is \(3075/8\), so (378.1) gives

$$
 e\ge {3075/8-26\over1482}={2867\over11856}=c. \tag{378.2}
$$

## 379. The matched original optimum

**Theorem 379.1.** For every admissible entire profile in §375, the original classes \(\mathcal N_2\) and \(\mathcal O_2\) both have optimum selected-law error \(c=2867/11856\). The same twenty-schedule allocation in §376 attains the value in both classes.

*Proof.* Section 377 gives a mass-one complete (N) table and a mass-one stopped (O) table satisfying every finite cap row at \(e=c\), with the same positive endpoint law. The common-seed realization and the finite-pattern source witnesses turn these tables into original hard-two acquisitions. For (N), both requests are acquired even when the first reply is zero; for (O), the increasing pair stops at its first queried zero. The output labels are the actual \(\theta_j\), and the handoff is sourcewise measurable and almost surely finite. The tail identity handles every \(n>8\), including the closed tie \(a_9=c\) and every later tie.

Conversely, any original (N_2) or (O_2) acquisition with error \(e\) induces its complete finite eight-coordinate table. The source witnesses for every Boolean word force the rows used in (378.1), while the full original rule retains the one common seed and one schedule mass. Applying (378.2) gives \(e\ge c\). The upper and lower bounds coincide. This proves the theorem. \(\square\)

## 380. One-coordinate deletions at the endpoint

Set

$$
 b^*=b(43/64)=\frac1{64}(43,34,34,29,27,25,22,20).
$$

A one-coordinate restriction deletes an original coordinate, relabels the retained coordinates in order, and uses labels (0,\ldots ,7). The eight retained profiles and their common cap are

$$
\begin{array}{c|c}
\text{deleted coordinate}&\text{retained profile}\ \hline
1&(17/32,17/32,29/64,27/64,25/64,11/32,5/16)\\
2&(43/64,17/32,29/64,27/64,25/64,11/32,5/16)\\
3&(43/64,17/32,29/64,27/64,25/64,11/32,5/16)\\
4&(43/64,17/32,17/32,27/64,25/64,11/32,5/16)\\
5&(43/64,17/32,17/32,29/64,25/64,11/32,5/16)\\
6&(43/64,17/32,17/32,29/64,27/64,11/32,5/16)\\
7&(43/64,17/32,17/32,29/64,27/64,25/64,5/16)\\
8&(43/64,17/32,17/32,29/64,27/64,25/64,11/32)
\end{array}
$$

The following tables give stopped allocations for these eight restrictions. In each table, a row (S) has its displayed mass; after the colon, cells are listed in stopped order: one cell for the empty schedule, two cells (0|1) for a singleton, and three cells (0|10|11) for a pair. An omitted coordinate is zero. All vectors are sums of the indicated multiples of (e_j).

**Deletion 1.** Let \(\mathcal A_1\) consist of the following rows; the profile is \((17/32,17/32,29/64,27/64,25/64,11/32,5/16)\).

\(S=∅:\quad m_S=557/9920,\quad [557/9920e_0]\).
\(S=12:\quad m_S=1437/4960,\quad [259/1984e_0+1579/9920e_1 | 1437/4960e_2 | 177/992e_0+409/9920e_3+139/1984e_4]\).
\(S=13:\quad m_S=199/1984,\quad [199/1984e_1 | 199/1984e_3 | 199/1984e_0]\).
\(S=14:\quad m_S=15/496,\quad [15/496e_1 | 15/496e_4 | 15/496e_0]\).
\(S=15:\quad m_S=15/496,\quad [15/496e_1 | 15/496e_5 | 15/496e_0]\).
\(S=23:\quad m_S=199/1984,\quad [139/1984e_0+15/496e_2 | 199/1984e_3 | 199/1984e_0]\).
\(S=24:\quad m_S=15/496,\quad [15/496e_0 | 15/496e_4 | 15/496e_0]\).
\(S=25:\quad m_S=15/496,\quad [15/496e_0 | 15/496e_5 | 15/496e_0]\).
\(S=34:\quad m_S=397/4960,\quad [397/4960e_0 | 397/4960e_4 | 501/9920e_0+39/4960e_5+3/2480e_6+203/9920e_7]\).
\(S=35:\quad m_S=501/9920,\quad [501/9920e_0 | 501/9920e_5 | 501/9920e_0]\).
\(S=36:\quad m_S=201/9920,\quad [201/9920e_0 | 201/9920e_6 | 201/9920e_0]\).
\(S=45:\quad m_S=15/248,\quad [15/248e_0 | 15/248e_5 | 501/9920e_0+99/9920e_6]\).
\(S=46:\quad m_S=201/9920,\quad [201/9920e_0 | 201/9920e_6 | 201/9920e_0]\).
\(S=56:\quad m_S=801/9920,\quad [801/9920e_0 | 801/9920e_6 | 201/9920e_0+15/248e_7]\).
\(S=67:\quad m_S=201/9920,\quad [201/9920e_0 | 201/9920e_7 | 201/9920e_0]\).

**Deletion 2.** Let \(\mathcal A_2\) consist of the following rows; the profile is \((43/64,17/32,29/64,27/64,25/64,11/32,5/16)\).

\(S=∅:\quad m_S=457/9920,\quad [457/9920e_0]\).
\(S=1:\quad m_S=5/496,\quad [5/496e_1 | 5/496e_0]\).
\(S=12:\quad m_S=1437/4960,\quad [1437/4960e_1 | 1437/4960e_2 | 177/992e_0+409/9920e_3+139/1984e_4]\).
\(S=13:\quad m_S=199/1984,\quad [199/1984e_1 | 199/1984e_3 | 199/1984e_0]\).
\(S=14:\quad m_S=15/496,\quad [15/496e_1 | 15/496e_4 | 15/496e_0]\).
\(S=15:\quad m_S=15/496,\quad [15/496e_1 | 15/496e_5 | 15/496e_0]\).
\(S=23:\quad m_S=199/1984,\quad [139/1984e_0+15/496e_2 | 199/1984e_3 | 199/1984e_0]\).
\(S=24:\quad m_S=15/496,\quad [15/496e_0 | 15/496e_4 | 15/496e_0]\).
\(S=25:\quad m_S=15/496,\quad [15/496e_0 | 15/496e_5 | 15/496e_0]\).
\(S=34:\quad m_S=397/4960,\quad [397/4960e_0 | 397/4960e_4 | 501/9920e_0+39/4960e_5+3/2480e_6+203/9920e_7]\).
\(S=35:\quad m_S=501/9920,\quad [501/9920e_0 | 501/9920e_5 | 501/9920e_0]\).
\(S=36:\quad m_S=201/9920,\quad [201/9920e_0 | 201/9920e_6 | 201/9920e_0]\).
\(S=45:\quad m_S=15/248,\quad [15/248e_0 | 15/248e_5 | 501/9920e_0+99/9920e_6]\).
\(S=46:\quad m_S=201/9920,\quad [201/9920e_0 | 201/9920e_6 | 201/9920e_0]\).
\(S=56:\quad m_S=801/9920,\quad [801/9920e_0 | 801/9920e_6 | 201/9920e_0+15/248e_7]\).
\(S=67:\quad m_S=201/9920,\quad [201/9920e_0 | 201/9920e_7 | 201/9920e_0]\).

**Deletion 3.** Let \(\mathcal A_3\) consist of the following rows; the profile is \((43/64,17/32,29/64,27/64,25/64,11/32,5/16)\).

\(S=∅:\quad m_S=457/9920,\quad [457/9920e_0]\).
\(S=1:\quad m_S=5/496,\quad [5/496e_1 | 5/496e_0]\).
\(S=12:\quad m_S=1437/4960,\quad [1437/4960e_1 | 1437/4960e_2 | 177/992e_0+409/9920e_3+139/1984e_4]\).
\(S=13:\quad m_S=199/1984,\quad [199/1984e_1 | 199/1984e_3 | 199/1984e_0]\).
\(S=14:\quad m_S=15/496,\quad [15/496e_1 | 15/496e_4 | 15/496e_0]\).
\(S=15:\quad m_S=15/496,\quad [15/496e_1 | 15/496e_5 | 15/496e_0]\).
\(S=23:\quad m_S=199/1984,\quad [139/1984e_0+15/496e_2 | 199/1984e_3 | 199/1984e_0]\).
\(S=24:\quad m_S=15/496,\quad [15/496e_0 | 15/496e_4 | 15/496e_0]\).
\(S=25:\quad m_S=15/496,\quad [15/496e_0 | 15/496e_5 | 15/496e_0]\).
\(S=34:\quad m_S=397/4960,\quad [397/4960e_0 | 397/4960e_4 | 501/9920e_0+39/4960e_5+3/2480e_6+203/9920e_7]\).
\(S=35:\quad m_S=501/9920,\quad [501/9920e_0 | 501/9920e_5 | 501/9920e_0]\).
\(S=36:\quad m_S=201/9920,\quad [201/9920e_0 | 201/9920e_6 | 201/9920e_0]\).
\(S=45:\quad m_S=15/248,\quad [15/248e_0 | 15/248e_5 | 501/9920e_0+99/9920e_6]\).
\(S=46:\quad m_S=201/9920,\quad [201/9920e_0 | 201/9920e_6 | 201/9920e_0]\).
\(S=56:\quad m_S=801/9920,\quad [801/9920e_0 | 801/9920e_6 | 201/9920e_0+15/248e_7]\).
\(S=67:\quad m_S=201/9920,\quad [201/9920e_0 | 201/9920e_7 | 201/9920e_0]\).

**Deletion 4.** Let \(\mathcal A_4\) consist of the following rows; the profile is \((43/64,17/32,17/32,27/64,25/64,11/32,5/16)\).

\(S=∅:\quad m_S=9/1216,\quad [9/1216e_0]\).
\(S=12:\quad m_S=23/76,\quad [27/1216e_0+341/1216e_1 | 23/76e_2 | 371/2432e_0+179/2432e_3+153/2432e_4+33/2432e_5]\).
\(S=13:\quad m_S=291/2432,\quad [291/2432e_1 | 291/2432e_3 | 291/2432e_0]\).
\(S=14:\quad m_S=105/2432,\quad [105/2432e_1 | 105/2432e_4 | 105/2432e_0]\).
\(S=15:\quad m_S=25/2432,\quad [25/2432e_1 | 25/2432e_5 | 25/2432e_0]\).
\(S=23:\quad m_S=291/2432,\quad [291/2432e_0 | 291/2432e_3 | 291/2432e_0]\).
\(S=24:\quad m_S=105/2432,\quad [105/2432e_0 | 105/2432e_4 | 105/2432e_0]\).
\(S=25:\quad m_S=25/2432,\quad [25/2432e_2 | 25/2432e_5 | 25/2432e_0]\).
\(S=34:\quad m_S=33/608,\quad [33/608e_0 | 33/608e_4 | 55/1216e_0+11/1216e_5]\).
\(S=35:\quad m_S=23/304,\quad [23/304e_0 | 23/304e_5 | 55/1216e_0+37/1216e_7]\).
\(S=36:\quad m_S=85/2432,\quad [85/2432e_0 | 85/2432e_6 | 85/2432e_0]\).
\(S=45:\quad m_S=65/1216,\quad [65/1216e_0 | 65/1216e_5 | 55/1216e_0+5/608e_7]\).
\(S=46:\quad m_S=85/2432,\quad [85/2432e_0 | 85/2432e_6 | 85/2432e_0]\).
\(S=56:\quad m_S=135/2432,\quad [135/2432e_0 | 135/2432e_6 | 85/2432e_0+25/1216e_7]\).
\(S=67:\quad m_S=85/2432,\quad [85/2432e_0 | 85/2432e_7 | 85/2432e_0]\).

**Deletion 5.** Let \(\mathcal A_5\) consist of the following rows; the profile is \((43/64,17/32,17/32,29/64,25/64,11/32,5/16)\).

\(S=∅:\quad m_S=1/304,\quad [1/304e_0]\).
\(S=12:\quad m_S=181/608,\quad [31/1216e_0+331/1216e_1 | 181/608e_2 | 47/304e_0+13/304e_3+121/1216e_4+1/1216e_5]\).
\(S=13:\quad m_S=81/608,\quad [81/608e_1 | 81/608e_3 | 81/608e_0]\).
\(S=14:\quad m_S=5/152,\quad [5/152e_1 | 5/152e_4 | 5/152e_0]\).
\(S=15:\quad m_S=7/608,\quad [7/608e_1 | 7/608e_5 | 7/608e_0]\).
\(S=23:\quad m_S=81/608,\quad [81/608e_0 | 81/608e_3 | 81/608e_0]\).
\(S=24:\quad m_S=5/152,\quad [5/152e_0 | 5/152e_4 | 5/152e_0]\).
\(S=25:\quad m_S=7/608,\quad [7/608e_2 | 7/608e_5 | 7/608e_0]\).
\(S=34:\quad m_S=5/76,\quad [5/76e_0 | 5/76e_4 | 27/608e_0+13/608e_5]\).
\(S=35:\quad m_S=3/38,\quad [3/38e_0 | 3/38e_5 | 27/608e_0+21/608e_7]\).
\(S=36:\quad m_S=5/152,\quad [5/152e_0 | 5/152e_6 | 5/152e_0]\).
\(S=45:\quad m_S=27/608,\quad [27/608e_0 | 27/608e_5 | 27/608e_0]\).
\(S=46:\quad m_S=5/152,\quad [5/152e_0 | 5/152e_6 | 5/152e_0]\).
\(S=56:\quad m_S=17/304,\quad [17/304e_0 | 17/304e_6 | 5/152e_0+7/304e_7]\).
\(S=67:\quad m_S=5/152,\quad [5/152e_0 | 5/152e_7 | 5/152e_0]\).

**Deletion 6.** Let \(\mathcal A_6\) consist of the following rows; the profile is \((43/64,17/32,17/32,29/64,27/64,11/32,5/16)\).

\(S=12:\quad m_S=271/928,\quad [51/1856e_0+491/1856e_1 | 271/928e_2 | 287/1856e_0+57/1856e_3+41/464e_4+17/928e_5]\).
\(S=13:\quad m_S=255/1856,\quad [255/1856e_1 | 255/1856e_3 | 255/1856e_0]\).
\(S=14:\quad m_S=57/1856,\quad [57/1856e_1 | 57/1856e_4 | 57/1856e_0]\).
\(S=15:\quad m_S=25/1856,\quad [25/1856e_1 | 25/1856e_5 | 25/1856e_0]\).
\(S=23:\quad m_S=255/1856,\quad [115/928e_0+25/1856e_2 | 255/1856e_3 | 255/1856e_0]\).
\(S=24:\quad m_S=57/1856,\quad [57/1856e_0 | 57/1856e_4 | 57/1856e_0]\).
\(S=25:\quad m_S=25/1856,\quad [25/1856e_0 | 25/1856e_5 | 25/1856e_0]\).
\(S=34:\quad m_S=9/116,\quad [9/116e_0 | 9/116e_4 | 41/928e_0+31/928e_5]\).
\(S=35:\quad m_S=17/232,\quad [17/232e_0 | 17/232e_5 | 41/928e_0+27/928e_7]\).
\(S=36:\quad m_S=57/1856,\quad [57/1856e_0 | 57/1856e_6 | 57/1856e_0]\).
\(S=45:\quad m_S=41/928,\quad [41/928e_0 | 41/928e_5 | 41/928e_0]\).
\(S=46:\quad m_S=57/1856,\quad [57/1856e_0 | 57/1856e_6 | 57/1856e_0]\).
\(S=56:\quad m_S=105/1856,\quad [105/1856e_0 | 105/1856e_6 | 57/1856e_0+3/116e_7]\).
\(S=57:\quad m_S=1/928,\quad [1/928e_0 | 1/928e_7 | 1/928e_0]\).
\(S=67:\quad m_S=57/1856,\quad [57/1856e_0 | 57/1856e_7 | 57/1856e_0]\).

**Deletion 7.** Let \(\mathcal A_7\) consist of the following rows; the profile is \((43/64,17/32,17/32,29/64,27/64,25/64,5/16)\).

\(S=∅:\quad m_S=1/1856,\quad [1/1856e_0]\).
\(S=12:\quad m_S=511/1856,\quad [1/116e_0+495/1856e_1 | 511/1856e_2 | 461/3712e_0+339/3712e_3+111/1856e_4]\).
\(S=13:\quad m_S=97/928,\quad [97/928e_1 | 97/928e_3 | 97/928e_0]\).
\(S=14:\quad m_S=83/1856,\quad [83/1856e_1 | 83/1856e_4 | 83/1856e_0]\).
\(S=15:\quad m_S=93/3712,\quad [93/3712e_1 | 93/3712e_5 | 93/3712e_0]\).
\(S=23:\quad m_S=97/928,\quad [295/3712e_0+93/3712e_2 | 97/928e_3 | 97/928e_0]\).
\(S=24:\quad m_S=83/1856,\quad [83/1856e_0 | 83/1856e_4 | 83/1856e_0]\).
\(S=25:\quad m_S=93/3712,\quad [93/3712e_0 | 93/3712e_5 | 93/3712e_0]\).
\(S=34:\quad m_S=271/3712,\quad [271/3712e_0 | 271/3712e_4 | 105/1856e_0+27/1856e_5+7/3712e_6]\).
\(S=35:\quad m_S=105/1856,\quad [105/1856e_0 | 105/1856e_5 | 105/1856e_0]\).
\(S=36:\quad m_S=117/3712,\quad [117/3712e_0 | 117/3712e_6 | 117/3712e_0]\).
\(S=45:\quad m_S=259/3712,\quad [259/3712e_0 | 259/3712e_5 | 105/1856e_0+49/3712e_6]\).
\(S=46:\quad m_S=117/3712,\quad [117/3712e_0 | 117/3712e_6 | 117/3712e_0]\).
\(S=56:\quad m_S=303/3712,\quad [303/3712e_0 | 303/3712e_6 | 117/3712e_0+93/1856e_7]\).
\(S=67:\quad m_S=117/3712,\quad [117/3712e_0 | 117/3712e_7 | 117/3712e_0]\).

**Deletion 8.** Let \(\mathcal A_8\) consist of the following rows; the profile is \((43/64,17/32,17/32,29/64,27/64,25/64,11/32)\).

\(S=12:\quad m_S=17/64,\quad [17/64e_1 | 17/64e_2 | 7/64e_0+5/64e_3+5/64e_4]\).
\(S=13:\quad m_S=7/64,\quad [7/64e_1 | 7/64e_3 | 7/64e_0]\).
\(S=14:\quad m_S=1/32,\quad [1/32e_1 | 1/32e_4 | 1/32e_0]\).
\(S=15:\quad m_S=1/32,\quad [1/32e_1 | 1/32e_5 | 1/32e_0]\).
\(S=23:\quad m_S=7/64,\quad [5/64e_0+1/32e_2 | 7/64e_3 | 7/64e_0]\).
\(S=24:\quad m_S=1/32,\quad [1/32e_0 | 1/32e_4 | 1/32e_0]\).
\(S=25:\quad m_S=1/32,\quad [1/32e_0 | 1/32e_5 | 1/32e_0]\).
\(S=34:\quad m_S=5/64,\quad [5/64e_0 | 5/64e_4 | 1/16e_0+1/64e_7]\).
\(S=35:\quad m_S=1/16,\quad [1/16e_0 | 1/16e_5 | 1/16e_0]\).
\(S=36:\quad m_S=1/32,\quad [1/32e_0 | 1/32e_6 | 1/32e_0]\).
\(S=45:\quad m_S=1/16,\quad [1/16e_0 | 1/16e_5 | 1/16e_0]\).
\(S=46:\quad m_S=1/32,\quad [1/32e_0 | 1/32e_6 | 1/32e_0]\).
\(S=56:\quad m_S=3/32,\quad [3/32e_0 | 3/32e_6 | 1/32e_0+1/16e_7]\).
\(S=67:\quad m_S=1/32,\quad [1/32e_0 | 1/32e_7 | 1/32e_0]\).

For each (mathcal A_i), the masses in the displayed rows sum to one and each cell has that mass. Directly grouping all (2^7-1) zero words by their first zero gives the following minimum slacks, in the order (A,C,P) for (n=1,ldots ,7); the final entry is the positive-word slack. This is a compact certificate for every row, since each number is the minimum of the corresponding left side minus its literal demand.

$$
\begin{array}{c|c|c|c|c|c|c|c}
 i&n=1&n=2&n=3&n=4&n=5&n=6&n=7&T\\ \hline
1,2,3&(15/64,229/9920,229/9920)&(15/64,229/9920,229/9920)&(15/64,229/9920,229/9920)&(271/992,229/9920,307/4960)&(135/496,229/9920,151/2480)&(759/2480,229/9920,47/496)&(391/1240,229/9920,129/1240)&229/9920\\
4&(15/64,39/2432,39/2432)&(15/64,39/2432,39/2432)&(15/64,39/2432,39/2432)&(15/64,39/2432,39/2432)&(599/2432,39/2432,17/608)&(155/608,39/2432,89/2432)&(357/1216,39/2432,183/2432)&39/2432\\
5&(15/64,15/1216,15/1216)&(15/64,15/1216,15/1216)&(15/64,15/1216,15/1216)&(169/608,15/1216,17/304)&(151/608,15/1216,1/38)&(313/1216,15/1216,43/1216)&(355/1216,15/1216,85/1216)&15/1216\\
6&(15/64,1/116,1/116)&(15/64,1/116,1/116)&(15/64,1/116,1/116)&(65/232,1/116,101/1856)&(519/1856,1/116,25/464)&(481/1856,1/116,31/928)&(537/1856,1/116,59/928)&1/116\\
7&(15/64,13/3712,13/3712)&(15/64,13/3712,13/3712)&(15/64,13/3712,13/3712)&(875/3712,13/3712,9/1856)&(925/3712,13/3712,17/928)&(139/464,13/3712,255/3712)&(33/116,13/3712,199/3712)&13/3712\\
8&(15/64,0,0)&(15/64,0,0)&(15/64,0,0)&(15/64,0,0)&(15/64,0,0)&(19/64,0,1/16)&(5/16,0,5/64)&0
\end{array}
$$

Every entry is nonnegative, so each deletion is feasible at \(15/64\). The rows with zero slack are allowed closed ties. These are feasibility witnesses only; no deletion optimum is asserted.

## 381. Why independent restrictions do not certify the full profile

**Theorem 381.1 (Endpoint obstruction).** At \(b^*\), every one-coordinate deletion is stopped-feasible at \(15/64\), whereas the full eight-coordinate profile is infeasible there. The gap is

$$
 c-{15\over64}={353\over47424}>0.
$$

*Proof.* The eight allocations in §380 prove the first assertion by their common masses and the nonnegative slack table. For the full profile, any complete (N) allocation at \(15/64\) would satisfy the rows used by the zero-cost score \(Y\). Applying (378.1) at \(b^*\) would give \(15/64\ge c\), contradicting the displayed positive gap. Hence the full finite (N) profile is infeasible, and therefore the original \(N_2\) profile is infeasible as well: every finite Boolean word used in the score has an actual source, and the one source-independent seed induces the complete finite table.

If a restriction deletes still more coordinates, start with the allocation for any one deleted coordinate, set every further deleted reply to \(1\), and project every output label belonging to a deleted coordinate to label \(0\). For each retained word, the base coordinate and the independent union coordinate can only increase, while the retained correct coordinate is unchanged; the positive-word base also increases. Contracting fixed replies preserves increasing stopped schedules, equal cell masses, and the one common seed. Thus every smaller finite restriction remains feasible at \(15/64\). The obstruction therefore defeats the whole strategy of certifying the eight-coordinate profile by independently feasible proper restrictions. It does not compare the unrestricted original \(N_2\) and \(O_2\) classes and does not provide a strict same-profile (N/O) separation. \(\square\)

## 382. Resource and interpretation boundaries

The allocation and score retain the full carrier of labels, all multiple-zero words, signed singleton demands, the independently charged union row, actual independent stopped cells, and literal affine mass. A finite positive word is only a table endpoint; the entire positive ordered vanishing tail is handled by (373.1), including \(a_9=c\) and later equalities. The source assumptions are exactly the divisibility source of [XXIII 368.1], the one-seed hard-two interfaces of [XXII 363.2], and the common-table realization of [XXIII 368.2].

Deletion caps are witnesses of feasibility after relabelling the retained coordinates. They are not deletion optima, and the projection argument does not create an original competitor on the same eight-coordinate profile. The result supplies no unrestricted joint selector at \(L\ge8\), no strict same-profile all-original-\(\mathcal O\) separator, no nonatomic-target conclusion, and no complete paid-\(M1\) conclusion. The finite marked laws remain supported on \(\{\theta_0,\ldots,\theta_8\}\), so they do not approximate the unchanged nonatomic targets.

The finite Boolean-table construction uses the exact common-seed transport in [XXIII 368.2], the independent TV rows and tail identity in [XXII 363.3–363.4], and the literal affine bound in [XXIII 368.3–368.4]. The lower inequality is a direct nonnegative score pairing; it uses no convex-mixing, padding, moment, radial, deficiency, or archived-\(p_t\) principle as a new standalone result.

## 383. Mathematical dependencies

The original source and finite-pattern witnesses are [Boundaries 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows). The complete common-seed and stopped-table interfaces are [108.1 and 110.1–110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#108-common-probability-vector-kernels-and-stopped-schedules), [Source-Correlated Laws 45](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#45-lawful-acquisition-through-one-inherited-seed), and [XXIII 368.2–368.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXIII.md). The finite tail transport is [XXIII 373.1]. The score support bound and signed residual notation are [XXIII 368.3–368.4]. No claim here changes the unresolved universal comparison in [XXIII 373.2–373.3].

## 追加锚（本行以下为增补区）
