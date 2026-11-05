using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class NarrowDoublingOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary odd-modulus narrow doubling orbits, the exact fixed-Q one-period-block consumer and abstract existence, checked by scoped Lean compilation. Full Circle J remains OPEN.",
        H("Actual doubling cycles and directed adjacent gaps"),
        Blocks(
            Paragraph(Text(
                "Scope. All orbit points use the original standard representatives modulo odd X. The results derive the Mersenne reduced denominator, exact diameter and explicit unit-shift numerator from the actual arbitrary-seed orbit, and characterize exactly when a prescribed seed anchors the narrow interval. The period and gcd scale in the converse are conclusions of the constructed orbit. This is finite cyclic order, modular arithmetic, least-period and gcd mathematics. No literature novelty, official acceptance or physical Circle J realization is claimed.")),
            Describe.Lean(DescribeId.Create("all-odd-modulus-classification"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/NarrowDoublingOrbit.narrow_classification"),
                H("Arbitrary-seed classification"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem assumes X>=3 odd, 0<Q<X and 2W<X, where W is the ordinary standard-residue orbit diameter. It concludes r>=2, r=orderOf(2 : ZMod D), D=2^r-1 and 2W=X-gcd(X,Q), where D=X/gcd(X,Q) and r is Function.minimalPeriod for doubling at Q in ZMod X. Nonunit Q is included. No proposed period, prime or Mersenne modulus, unit seed, transitivity, gap recurrence or classification is a replacement hypothesis.")),
                    Paragraph(Text(
                        "The retained original proof cancels exactly gcd(X,Q) in the return congruence. Its narrow-interval doubling branches preserve strict circular order and give a shift of the sorted actual orbit. New source transfers the actual temporal orbit to a sorted-index doubling map p: induction identifies its n-th point from temporal phase m with R(m+n), where R(n)=(2^n Q) mod X. The existing phase-block coverage supplies every target; minimal-period injectivity modulo r proves the r-th return and excludes all earlier positive returns. Thus the single r-cycle is derived. Shift arithmetic proves p commutes with adjacent successor, giving the actual action on directed adjacent gaps.")),
                    Paragraph(Text(
                        "New source defines each integer directed gap as adjacent endpoint difference, adding X only at the last sorted index. The wrap gap is L=X-W>X/2; every other gap is positive and has twice its length below X. Directed endpoint congruences and successor commutation yield G(p(i)) congruent to 2G(i) modulo X. Proved bounds identify this exactly as 2G(i) off the wrap, and 2L-X at the wrap. With d=G(p(wrap)), induction along the derived r-cycle gives G(p^(n+1)(wrap))=2^n*d for n<r. At return, L=2^(r-1)*d, hence X=(2^r-1)*d and d=X-2W>0.")),
                    Paragraph(Text(
                        "All actual residues and X are divisible by g=gcd(X,Q), so g divides each directed gap, including d. The actual return gives D|(2^r-1). Writing d=g*u in integers and cancelling positive g from X=gD=(2^r-1)d gives (2^r-1)|D. Antisymmetry gives D=2^r-1, cancellation gives d=g, and 2W=X-g follows. The generic gap-cycle helper is consumed after its actual cycle and recurrence hypotheses are derived from the original narrowness assumptions. These proof terms are included in the successful scoped Lean build."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-orbit-explicit-numerator"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/NarrowDoublingOrbit.narrow_explicit_numerator"),
                H("Explicit reconstruction of the actual narrow orbit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For odd X>=3, 0<Q<X and standard-residue diameter W with 2W<X, put r=period(X,Q) and g=gcd(X,Q). The theorem derives a shift 0<s<r, coprimality of s and r, and an inverse 0<=u<r with su=1 in ZMod r. Subtraction in e_i=[u(i+1)-1]_r takes place modulo r. Define delta_i=2^e_i, a_j=sum_(i<s)delta_i+sum_(i<j)delta_i and q=2^(r-1)+sum_(i<s-1)delta_i. The actual orbit equals {g*a_j:0<=j<r}, and its greatest element is g*q.")),
                    Paragraph(Text(
                        "This uses the derived sorted cycle and the existing directed-gap growth proof. Transitivity produces the inverse by reaching sorted index 1 from index 0. Multiplying the exponent formula by s identifies the original sorted gap at each index, including the long final gap. Doubling the least sorted point cannot wrap, since its image would then be smaller than that least point. Its unwrapped image at index s therefore fixes the minimum as the first s gaps; telescoping recovers every point. The gap at s-1 has exponent zero, giving the displayed maximum.")),
                    Paragraph(Text(
                        "The seed Q may occupy any sorted position. Equality Q=g*q additionally requires Q to be the orbit maximum, as in the anchored interval condition; X=3,Q=1 must not be assigned q(2,1)=2. A Mersenne denominator and maximality alone do not imply narrowness, as X=31,Q=24 shows. The anchored classification below supplies the converse construction and the exact interval criterion. Uniqueness, counting and any common physical permutation realization remain separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("anchored-explicit-classification"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/NarrowDoublingOrbit.anchored_explicit_classification"),
                H("Exact anchored unit-shift numerator criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every odd X>=3 and 0<Q<X, Anchored(X,Q) means that each actual residue R(n) satisfies R(n)<=Q and Q<=R(n)+(X-1)/2. These subtraction-free natural inequalities express precisely the integer interval [Q-(X-1)/2,Q]. The theorem identifies this condition with the existence of r>=2, 0<s<r, coprime(s,r), 0<=u<r, su=1 in ZMod r, M=2^r-1 dividing X, and Q=(X/M)*q(r,s,u). For every such arithmetic witness it also derives period(X,Q)=r and gcd(X,Q)=X/M. Neither equality is an assumption of the converse.")),
                    Paragraph(Text(
                        "For the construction, the affine exponent map i -> [u(i+1)-1]_r permutes 0,...,r-1. Thus the explicit gaps have total M; the final gap is 2^(r-1), and the gap at s-1 is 1. Their prefix sums give strictly increasing positive points below M with width 2^(r-1)-1 and final point q. In ZMod M, consecutive point differences are the prescribed gaps even across the seam. Shifting by s doubles these gap residues. The differences 2*a_j-a_(j+s) therefore have constant residue, zero at index 0 because a_s=2*a_0. This proves the actual doubling map of the constructed points.")),
                    Paragraph(Text(
                        "Multiplying the constructed representatives by X/M gives the exact orbit at modulus X. Inverting the index shift reaches every constructed point from its maximum; strict increase and positive scale identify the actual orbit cardinality and least period as r. The explicit width proves the anchored interval. Applying the original narrow denominator theorem to this constructed orbit then identifies its gcd scale. Conversely, the anchored interval makes Q the actual maximum and forces narrowness, so explicit reconstruction supplies the necessary numerator. The construction includes r=2,s=1. For X=15 the allowed parameters may have periods 2 and 4; uniqueness across a fixed X is not asserted.")),
                    Paragraph(Text(
                        "The conclusion concerns standard-residue arithmetic orbits. It does not construct a common physical sigma, nested masks, a literal fresh ear, full OriginalOrders, all natural repeated prefixes or physical J/C3.1. Those original physical obligations remain OPEN. No literature novelty or official acceptance is claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fixed-q-one-period-narrow-reduction"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/NarrowDoublingOrbit.fixedQ_block_forces_narrow"),
                H("One consecutive actual-period block covers every fixed-Q phase"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For one fixed Q with X+1<=2Q and Q<X, arbitrary k and starting layer m0, HeightBlock requires for every 0<=j<r that 0<=H(m0+j), 2H(m0+j)<=X-1 and H(m0+j)=Q-2^(k+m0+j)Q modulo X. The retained source identifies Q-H with the exact standard representative and reuses cycAdd_bijective from AssociatedMersenne.CircularWords to cover the whole orbit. The source retains exact period/order, interval containment, Q as an orbit maximum and strict narrowness. It now also includes the sorted shift's derived transitivity, actual r-th return and lack of earlier positive return."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-fixed-q-block-consumer"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/NarrowDoublingOrbit.fixedQ_block_classification"),
                H("The exact fixed-Q block consumer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With the same odd X>=3, fixed nonterminal Q, arbitrary k,m0 and ONE consecutive block of the actual period r, the theorem consumes the reduction and classification to conclude D=2^r-1 and 2W=X-gcd(X,Q). It requires neither all blocks nor a longer chosen return time. It is necessary abstract arithmetic, with no physical Circle construction or proof of the physical interface here."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("some-narrow-orbit-from-mersenne-divisor"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/NarrowDoublingOrbit.exists_narrow_of_mersenne_dvd"),
                H("An existentially chosen seed of exactly the specified period"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The construction takes t>=2 and M=2^t-1 dividing X, choosing Q=X/M. Before time t its representatives are Q,2Q,...,2^(t-1)Q, all below X; time t returns to Q. Strict power growth excludes every earlier positive return, giving actual period and cardinality t. The extrema give 2W=X-Q<X. This constructs SOME abstract orbit; it supplies no sufficient criterion for a prescribed Q."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-period-existence-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/NarrowDoublingOrbit.exists_narrow_period_iff_mersenne_dvd"),
                H("Existence with a specified actual period"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each odd X>=3 and t>=2, the theorem states that some 0<Q<X has actual period t and 2W<X if and only if 2^t-1 divides X. Necessity consumes the arbitrary-seed classification; sufficiency consumes the retained existential construction. This equivalence is included in the successful scoped Lean build."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("abstract-existence-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/NarrowDoublingOrbit.exists_narrow_iff_mersenne_dvd"),
                H("Abstract existence when the period is not prescribed"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equivalence states that some 0<Q<X has a narrow actual orbit if and only if some t>=2 has 2^t-1 dividing X. It does not assert prescribed-Q sufficiency: for example X=31,Q=24 has orbit {3,6,12,17,24}, with Q maximal but diameter 21>31/2."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Remaining verification and scope. The eight arithmetic endpoints have compiled, including the anchored prescribed-Q arithmetic equivalence and the explicit numerator reconstruction. Three audits are declared_unresolved: narrow_classification at source.unsafe_or_external (Nat.gcd), anchored_explicit_classification at source.observation_data, and narrow_explicit_numerator at source.roles. The other five audits are absent; all eight unfinished audits are tracked under issue11434. No declared_validated audit or official acceptance is claimed. The arithmetic equivalence does not construct a common physical sigma or establish physical prescribed-Q realization. Nested masks, a literal fresh ear, both full OriginalOrders, all natural repeated and taken prefixes, and full Circle J remain OPEN. Sparse layers, varying Q and terminal Q=X are outside the stated arithmetic domain."))),
        []));
}
