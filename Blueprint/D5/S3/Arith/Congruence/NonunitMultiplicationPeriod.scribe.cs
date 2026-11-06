using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

// Prepared exposition; native projector/emit has not been run. Lean kernel checks are separate.
internal sealed class NonunitMultiplicationPeriodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual multiplication orbit of a nonunit seed has the order of the multiplier on its effective quotient modulus.",
        H("Nonunit modular seeds: returns and least periods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonunit-multiplication-return-effective-modulus"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/NonunitMultiplicationPeriod.isPeriodicPt_mul_natCast_iff"),
                H("Exact returns without cancelling a nonunit in ZMod"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For natural M,u,t,e with M>0, let f(x)=u*x on ZMod(M), g=gcd(t,M) and Q=M/g. The statement is IsPeriodicPt(f,e,t) if and only if (u:ZMod(Q))^e=1. Iteration gives u^e*t, and ZMod.natCast_eq_natCast_iff translates its equality with t into a natural congruence. Nat.ModEq.cancel_right_div_gcd cancels the seed while dividing the modulus by its gcd. Conversely, multiplying a congruence modulo Q by g restores modulus M; multiplying its sides by t/g restores the seed. The equalities g*(t/g)=t and Q*g=M follow from gcd divisibility. No return equivalence is assumed as a premise.")),
                    Paragraph(Text(
                        "All exponents, including zero, are included. The multiplier may be zero or a nonunit, and t may be zero or a multiple of M. Congruences avoid the invalid natural-subtraction step u^e-1 when u=0 and e>0. Positive M is essential to the cancellation statement. This is a consumed bridge assembled from pinned Mathlib APIs; the gcd cancellation theorem is reused, not reproved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonunit-multiplication-minimal-period-effective-order"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/NonunitMultiplicationPeriod.minimalPeriod_mul_natCast"),
                H("The actual seed minimal period"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The actual Function.minimalPeriod of f at t equals orderOf(u:ZMod(Q)). The proof compares all return exponents with multiplication at one on ZMod(Q), using Function.minimalPeriod_eq_minimalPeriod_iff and the definition of orderOf. It assumes no positive return. If none exists, both conventions give zero. If t=0 then Q=1, and both sides are one; M=1 has the same boundary. This compares the original orbit with quotient return times without replacing its seed by a unit in the original modulus.")),
                    Paragraph(Text(
                        "The consumer is the full RadixFourNonunitZeroSubsets.seed21_separation itself. On exactly n>=3 and not 3 dividing n, its two gcd values are three. Set M=2^(2*n)-1 and u=2. PowerQuotientOrder.power_quotient_order at u=2,a=1,k=n gives orderOf(2:ZMod(M/3))=2*n, since n is not one. The generic bridge is applied to each actual seed t=3 and t=21 inside that conjunction. The original positivity, integer trace, complete zero-fibre classification and zero-subset counts four versus two retain all Fin(2*n) physical labels. No separate application theorem or duplicated quotient-order proof is introduced.")),
                    Paragraph(Text(
                        "Equal gcd and equal orbit length do not determine integer zero-sum geometry. Modular congruence erases multiples of M. In this family the sealed source gives the seed-21 even-label integer trace M and positive even terms; the seed-3 zero-subset count comes from TwoBitZeroSubsets. The period bridge supplies neither integer cancellation nor those counts. It says nothing about subset-rotation periods. Transferring the modular minimal period to TwoRunSource.period would additionally require a return equivalence between centered doubleStep at orbit(k,t,0) and multiplication on ZMod(2^k-1), with the integer/natural modulus casts and centered uniqueness justified. That centered-conjugacy statement is not supplied here.")),
                    Paragraph(Text(
                        "The Lean owner and its full consumer are checked in the targeted kernel stage against the fixed accepted candidate and compatible Lean 4.35/mathlib inputs. This Scribe remains prepared: native projector/emit was not run. Both generic public theorems and the amended consumer retain faithful Reg or concrete linked-issue obligations before official delivery. No review, novelty, registration, freeze, CI, merge or official-delivery acceptance is claimed."))),
                DescribeRole.Theorem)), []));
}
