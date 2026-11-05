using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class NarrowDoublingOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary odd-modulus narrow doubling orbits, the exact fixed-Q one-period-block consumer and abstract existence, checked by scoped Lean compilation. Full Circle J remains OPEN.",
        H("Actual doubling cycles and directed adjacent gaps"),
        Blocks(
            Paragraph(Text(
                "Status. Native scoped Lean compilation succeeded after the exact saved candidate was installed and actual elaboration errors were repaired. The original candidate bytes and command/error evidence are preserved outside the worktree. All six public results, including the actual gap cycle, recurrence and gcd denominator inference, were compiled. Axiom closure, fresh report binding, Reg realization and official acceptance remain separate checks. The supplied ordinary proofs were fallible inputs. This is elementary finite cyclic order, minimal-period and gcd mathematics; no literature novelty is claimed.")),
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
                    "The equivalence states that some 0<Q<X has a narrow actual orbit if and only if some t>=2 has 2^t-1 dividing X. It does not assert prescribed-Q sufficiency: for example X=31,Q=24 has orbit {3,6,12,17,24}, with Q maximal but diameter 21>31/2. This ordinary example was not rerun as a control in this assignment."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Remaining verification and scope. Scoped Lean compilation succeeded; report binding, axiom extraction and faithful Reg are being checked separately. No official check ran. No validated Reg registration is claimed by compilation alone. PR25303, PR24762 and PR24217 closeout is unchanged. The four-bit consumer is outside scope. Physical realization, nested masks, joint strip sufficiency, prescribed-Q sufficiency, sparse layers, varying Q, terminal Q=X and full Circle J remain OPEN or unclaimed. No new PR or external message is part of this work."))),
        []));
}
