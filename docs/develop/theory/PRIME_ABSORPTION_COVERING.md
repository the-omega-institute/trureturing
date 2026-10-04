# Height-coded prime absorption for distinct odd covers

## 1. Scope

This is a reference account of a finite construction for distinct odd covering systems. Its source is the height-coded absorption argument HPA3–HPA9 in the project's report on private congruence hulls and crossed modulus closure. It asserts ordinary mathematics; kernel verification is determined by the corresponding Lean declarations and their checked dependencies.

All source congruence tests use the literal original residues; output residues are chosen from the corresponding actual inverse images. A covering system of size $L$ is a family $(r_i,d_i)_{i<L}$ with pairwise distinct odd integers $d_i>1$ such that every natural number is congruent to some $r_i$ modulo $d_i$. By periodicity this is equivalent to covering every integer.

## 2. A strict reduction of the whole covering system

**theorem 2.1 (height-coded prime absorption).** Let $(r_i,d_i)_{i<L}$ be any distinct odd covering system, and suppose its least common multiple is $p^Hq^GM$, where $p,q$ are distinct odd primes, $H,G\ge1$, and $M$ is coprime to $pq$. Suppose one original modulus is $q$ and $q>p^{2H+1}$. Then there exist $L'<L$ and a distinct odd covering system of size $L'$. The construction is allowed to increase the height of $p$; it imposes no restriction on the primes, heights, or phases in $M$.

Proof. Put $b=H+1$ and $E_e=H+be$. Encode the first $E_1=2H+1$ base-$p$ digits injectively into the $q-1$ roots different from the residue of the original pure $q$ class. This fits because $p^{2H+1}<q$. Encode every subsequent block of $b$ base-$p$ digits into one $q$ digit; $p^b<q$. For every $1\le e\le G$ this gives one compatible family of injections

$$
\theta_e:\mathbb Z/p^{E_e}\mathbb Z\longrightarrow\mathbb Z/q^e\mathbb Z.
$$

Compatibility means $\theta_G(z)\bmod q^e=\theta_e(z\bmod p^{E_e})$. The same map is fixed before any original label or cofactor is selected.

For each output integer $z$, use the Chinese remainder theorem to obtain one source integer $\Psi(z)$ satisfying

$$
\Psi(z)\equiv z\pmod{p^HM},\qquad
\Psi(z)\equiv\theta_G(z)\pmod{q^G}.
$$

Every original modulus has a unique factorization $d_i=p^{a_i}q^{e_i}s_i$, where $a_i\le H$, $e_i\le G$, and $s_i\mid M$. If $e_i=0$, the complete inverse image of its class is its unchanged class. If $e_i>0$, the inverse image is either empty or a single arithmetic progression of modulus $p^{E_{e_i}}s_i$. Indeed the literal $q^{e_i}$ residue has at most one inverse prefix, the literal $p^{a_i}$ condition either agrees with this prefix or makes the inverse empty, and the literal $s_i$ condition is preserved.

For each nonempty inverse choose one point $c_i$ in it and enclose the entire inverse by the class

$$
z\equiv c_i\pmod{p^{(H+1)e_i+a_i}s_i}.
$$

This contains the inverse because $(H+1)e_i+a_i\le E_{e_i}$. It agrees with the original modulus when $e_i=0$. Every new modulus is odd and greater than one. For $e_i>0$ its $p$-height exceeds $H$, so it cannot collide with an unchanged label. More generally the replacement height $k=(H+1)e_i+a_i$ uniquely determines $a_i=k\bmod(H+1)$ and $e_i=k/(H+1)$; the part coprime to $p$ determines $s_i$. Equal replacement moduli therefore force equal original moduli and the same original index.

For every $z$, an original class covers $\Psi(z)$; that class has a nonempty inverse and its assigned enclosure covers $z$. Hence these enclosures cover all natural numbers. The original pure $q$ class has empty inverse because the first digit code avoids its actual root. At most one output class is assigned to every other original, so the output size is strictly less than $L$. This accounts for every original class through one source map, including classes with both $p$ and $q$ factors and all cofactor conditions.

## 3. Boundary

The theorem is a conditional strict reduction, not a proof that every distinct odd covering system is impossible. Using it to bound support primes requires a separately justified extremal comparison principle. The output need not preserve original heights, divisor closure, a specified palette, or the original least common multiple.

The classical Chinese remainder theorem, finite radix representations, and prime factorization are reused. The combined prefix code, height labels, and complete source transport supply the construction specific to this statement. No probability independence or equality between an individual private region and a simultaneous deletion hole is assumed.

## 追加锚（本行以下为增补区）

## 4. A complete prefix deletion and the private region of a pure power

**theorem 4.1 (complete prefix liability).** Let $I$ be a finite index set and let $A_i=[r_i]_{d_i}$ be arithmetic progressions covering all natural numbers. Let $q$ be prime, let $R>0$ be coprime to $q$, and suppose every positive modulus $d_i$ divides $q^G R$. Fix $0\le k<G$ and an index $j$ with $d_j=q^{k+1}$. Put

$$
\begin{aligned}
J&=\{i:q^{k+1}\mid d_i,\ r_i\equiv r_j\pmod{q^k}\},\\
E&=\mathbb N\setminus\bigcup_{i\notin J}A_i,\\
P_j&=A_j\setminus\bigcup_{i\ne j}A_i.
\end{aligned}
$$

Assume that for every $i\in J\setminus\{j\}$ the progression $A_i$ is not contained in $A_j$: explicitly there is a natural number in $A_i$ but outside $A_j$. Then, for every natural number $x$,

$$
x\in E
\quad\Longleftrightarrow\quad
x\equiv r_j\pmod{q^k}
\quad\text{and}\quad
\exists y\in P_j:\ y\equiv x\pmod R.
$$

Proof. Every deleted progression is contained in the parent cylinder $[r_j]_{q^k}$, so whole coverage puts $E$ inside that parent. Within the parent, each retained progression of $q$-height at most $k$ depends only on the fixed parent prefix and the residue modulo $R$. Every retained progression of larger $q$-height has a different parent prefix and is absent throughout the parent. Membership in $E$ therefore depends only on these preserved coordinates.

If another deleted progression met $A_j$, divisibility by $q^{k+1}$ would make it contained in $A_j$, contradicting the stated assumption. Consequently $E\cap A_j=P_j$. For any $x\in E$, the Chinese remainder theorem gives $y\equiv x\pmod R$ and $y\equiv r_j\pmod{q^{k+1}}$. The preserved-coordinate property puts $y$ in $E$, hence in $P_j$. Conversely a private point $y$ belongs to $E$, and any point in the parent with the same residue modulo $R$ belongs to $E$ by that same property.

The identity retains the complete $R$ coordinate and the literal original parent prefix. It makes no claim that arbitrary simultaneous deletions can be reconstructed from individual private regions. Neither oddness, pairwise distinctness of the moduli, nor nonemptiness of the private region is needed; irredundancy of the original family is a sufficient condition for the stated noncontainments.

## 追加锚 4（本行以下为后续增补区）

## 5. A terminal donor at bounded ternary height

**theorem 5.1 (terminal-donor descent).** Let $A_i=[r_i]_{d_i}$, indexed by a finite set $I$, cover all natural numbers, with $d_i>1$. Repeated or even moduli are allowed. Let $q$ be prime, let $G,k,W$ be natural numbers with $\gcd(W,3q)=1$, and suppose $d_i\mid 9q^GW$ for every $i$. Fix an actual index $j$ with $d_j=q^{k+1}$. Define its complete private region and ternary projection by

$$
P_j=A_j\setminus\bigcup_{i\ne j}A_i,
\qquad
\Lambda=\{x\bmod9:x\in P_j\},
\qquad s=|\Lambda|.
$$

If $q>27$ and $27s+1\le q+9$, then there is one finite indexed family $A'_i=[r'_i]_{d'_i}$, $i\in I'$, covering all natural numbers, with $d'_i>1$, such that

$$
|I'|\le |I|,
\qquad
\sum_{i\in I'}d'_i<\sum_{i\in I}d_i.
$$

For this same output family, pairwise distinctness of the input moduli implies pairwise distinctness of the output moduli, and oddness of all input moduli implies oddness of all output moduli. No irredundancy or extremality assumption is required.

Proof. If $s=0$, the donor has no private point and can be deleted. More generally, if another class contained in $A_j$ can be deleted, this also proves the conclusion. Thus assume $s>0$ and that every other class in

$$
J=\{i:q^{k+1}\mid d_i,\ r_i\equiv r_j\pmod{q^k}\}
$$

has a point outside $A_j$. Put $u=r_j\bmod q^k$ and retain exactly the classes outside $J$. Theorem 4.1 with $R=9W$ identifies their full deletion hole $E$ as the chosen parent with precisely those complete $9W$ residues attained in $P_j$. In particular, every point of $E$ has its old residue modulo $9$ in $\Lambda$. The donor and period conditions imply $k<G$.

Over the $s$ old ternary words in $\Lambda$, there are $27s$ prefixes of depth five. Choose one depth-three prefix extending a word in $\Lambda$ and replace its nine depth-five descendants by that one short leaf. This partitions the entire forest into $N=27s-8$ leaves. Assign the short leaf the donor's actual next $q$ digit and inject the other $N-1$ leaves into the other $q-1$ digits. The capacity hypothesis supplies this injection. The short leaf terminates. On each continuing leaf encode each subsequent block of three ternary digits into one $q$ digit; $27<q$ permits this for every remaining level. All assignments are fixed on the entire forest, independently of the cofactor coordinate and of the original owner.

For an output point in the parent and forest, use the Chinese remainder theorem to form one source preserving its complete $9W$ coordinate and parent $u$. On a continuing leaf its remaining $q$ digits are the encoded digits. On the terminal leaf its next digit is the donor's and the later digits can be fixed arbitrarily. Theorem 4.1 implies that a point in $E$ is sent to another point in $E$. The terminal leaf is covered by the new class with parent $u$, the chosen ternary prefix, and modulus $27q^k$.

Each deleted modulus has a factorization $d_i=3^{a_i}q^{k+t_i}m_i$, where $0\le a_i\le2$, $1\le t_i\le G-k$, and $m_i\mid W$. Its literal $q$ prefix selects at most one continuing prefix of depth $2+3t_i$. That prefix already lies over one old word of $\Lambda$. Preserving the old ternary coordinate either satisfies the original $3^{a_i}$ condition or makes the inverse empty. Preserving $W$ gives exactly the original $m_i$ phase. Thus each nonempty continuing inverse is one progression with the parent, this ternary prefix, and the original cofactor phase; there is no additional projection mask. Enclose it by the class with modulus

$$
M_i=3^{3t_i+a_i}q^km_i.
$$

The enclosure contains the inverse since $3t_i+a_i\le2+3t_i$. Every new modulus has ternary height at least three, whereas all retained moduli have ternary height at most two. Among new moduli, the ternary exponent recovers $a_i$ and $t_i$ by remainder and quotient modulo three, and the cofactor recovers $m_i$. Equal new labels therefore imply equal original moduli. The donor occupies the slot $t_i=1,a_i=0,m_i=1$ and has no continuing inverse because its next digit is assigned only to the terminal leaf. Consequently input numerical distinctness implies output numerical distinctness. Each new modulus is a nonunit, and odd input moduli give odd output moduli.

For any continuing output in $E$, original whole coverage of its source supplies an owner in $J$, so the corresponding enclosure covers the output. Terminal outputs are covered directly, and outside $E$ the retained family already covers. There is at most one new class per deleted index. The donor contributes one, so the selected deleted indices form a nonempty subset $I_0\subseteq J$. For every selected index, including the donor,

$$
M_i=27^{t_i}(3^{a_i}q^km_i)
<q^{t_i}(3^{a_i}q^km_i)=d_i.
$$

The unchanged retained indices and the selected replacements therefore give $|I'|\le|I|$ and a strictly smaller sum of numerical moduli. Both preservation implications concern this same constructed family.

## 追加锚 5（本行以下为后续增补区）
