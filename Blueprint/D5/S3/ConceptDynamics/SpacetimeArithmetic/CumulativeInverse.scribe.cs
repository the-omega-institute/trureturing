using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeArithmetic;

internal sealed class CumulativeInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer-time cumulative histories have an exact adjacent-difference inverse.",
        H("Cumulative histories and the difference inverse"),
        Blocks(
            Paragraph(Text(
                "Cumulative summation records all past increments at every integer time. The admissible "
                    + "histories have a zero left tail and a constant right tail, which may be nonzero. "
                    + "The construction first works for any additive commutative coefficient group and "
                    + "then specializes to the original jointly finite time-space profiles.")),
            Describe.Lean(
                DescribeId.Create("signal"),
                DeclarationHandle.Create(Prefix + "Signal"),
                H("Finitely supported increments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Signal R consists of R-valued increments indexed by all integers, with only finitely many "
                        + "nonzero time components."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tail-condition"),
                DeclarationHandle.Create(Prefix + "TailCondition"),
                H("Zero left tail and constant right tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A history has integer thresholds l and u and a value B. Every value before l is zero, and "
                        + "every value at or after u equals B. The final constant B may be nonzero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("history"),
                DeclarationHandle.Create(Prefix + "History"),
                H("Admissible cumulative histories"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "History R is the subtype of all integer-indexed R-valued sequences satisfying both tail "
                        + "conditions. Pointwise addition uses the smaller left threshold and the larger right "
                        + "threshold; pointwise negation preserves the thresholds. These operations give an additive "
                        + "commutative group."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cumulative"),
                DeclarationHandle.Create(Prefix + "cumulative"),
                H("Cumulative sum over the finite past support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At integer time n, cumulative c sums c t over the finite support entries t with t at most "
                        + "n. This is a finite sum at every time, including negative times."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cumulative-succ"),
                DeclarationHandle.Create(Prefix + "cumulative_succ"),
                H("One time step adds its increment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The support entries at most n consist of the entries at most n minus one together with the "
                        + "increment at n when it is nonzero. Thus the current cumulative value equals its "
                        + "predecessor plus c n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cumulative-history"),
                DeclarationHandle.Create(Prefix + "cumulativeHistory"),
                H("Cumulative sums satisfy both tails"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonempty support, its minimum gives a zero left tail and its maximum gives an eventual "
                        + "constant right tail equal to the total sum. Empty support gives the zero history."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("difference-finite"),
                DeclarationHandle.Create(Prefix + "difference_finite"),
                H("Both tails force finite difference support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The adjacent difference vanishes before the left threshold because both values are zero, "
                        + "and after the right threshold because both values are B. Its support is contained in a "
                        + "finite integer interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("difference"),
                DeclarationHandle.Create(Prefix + "difference"),
                H("Adjacent differences as a finite signal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The value at n is the history value at n minus its value at n minus one. The proved finite "
                        + "support makes this an element of Signal R."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("difference-apply"),
                DeclarationHandle.Create(Prefix + "difference_apply"),
                H("The difference formula at every integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluation of the finite signal produced by difference is exactly the adjacent subtraction "
                        + "at the chosen integer time."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("difference-cumulative"),
                DeclarationHandle.Create(Prefix + "difference_cumulative"),
                H("Differences recover every finite signal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying difference after cumulativeHistory recovers the original increment profile at "
                        + "every integer, using the one-step recurrence and additive cancellation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cumulative-difference"),
                DeclarationHandle.Create(Prefix + "cumulative_difference"),
                H("Cumulative sums recover every admissible history"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equal adjacent differences and a shared zero point on the left imply equal histories: "
                        + "natural-number induction reaches every time to the right, and the left tail handles "
                        + "earlier times. Applying this uniqueness argument to the differences of C proves exact "
                        + "recovery of C."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cumulative-add"),
                DeclarationHandle.Create(Prefix + "cumulative_add"),
                H("Cumulative summation preserves addition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Adjacent differences preserve pointwise addition. Uniqueness of a history with those "
                        + "differences and the zero left tail therefore makes the cumulative history of a sum equal "
                        + "to the sum of cumulative histories."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cumulative-equiv"),
                DeclarationHandle.Create(Prefix + "cumulativeEquiv"),
                H("The additive equivalence for coefficient groups"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cumulative and difference operators, the two inverse identities, and preservation of "
                        + "addition form an additive equivalence for every additive commutative coefficient group."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cumulative-inverse-bijective"),
                DeclarationHandle.Create(Prefix + "cumulative_inverse_bijective"),
                H("Bijectivity of cumulative summation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The additive equivalence supplies injectivity and surjectivity of cumulativeHistory on the "
                        + "full integer-time carriers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("space"),
                DeclarationHandle.Create(Prefix + "Space"),
                H("Three-dimensional integer space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A spatial point has three integer coordinates, represented by a function from Fin 3 to the "
                        + "integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spatial"),
                DeclarationHandle.Create(Prefix + "Spatial"),
                H("Finite spatial coefficient profiles"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A spatial coefficient is an integer-valued function on the three-dimensional lattice with "
                        + "finite support. This theorem uses its additive group structure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile"),
                DeclarationHandle.Create(Prefix + "Profile"),
                H("Jointly finite time-space profiles"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A profile has integer coefficients indexed by integer time and a spatial point. Its joint "
                        + "time-space support is finite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-cumulative-equiv"),
                DeclarationHandle.Create(Prefix + "profileCumulativeEquiv"),
                H("The equivalence on the original time-space carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib Finsupp.curryAddEquiv identifies joint finite support with finitely many finitely "
                        + "supported spatial components. Composing it with cumulativeEquiv gives the additive "
                        + "equivalence on time-space profiles."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-cumulative-apply"),
                DeclarationHandle.Create(Prefix + "profile_cumulative_apply"),
                H("The forward map is the stated cumulative sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At time n, the time-space equivalence evaluates to the cumulative sum of the curried "
                        + "spatial increments through n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-inverse-apply"),
                DeclarationHandle.Create(Prefix + "profile_inverse_apply"),
                H("The inverse formula at each time-space coordinate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inverse profile at a pair consisting of time n and spatial point p equals C n p minus "
                        + "C at n minus one and p. Uncurrying preserves joint finite support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cumulative-inverse"),
                DeclarationHandle.Create(Prefix + "cumulative_inverse"),
                H("Additive bijection with the difference inverse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On jointly finitely supported profiles, cumulative summation is bijective and preserves "
                        + "addition, and its inverse is adjacent subtraction at every integer time and every spatial "
                        + "point. The target retains both tail conditions and its pointwise additive group structure."))),
                DescribeRole.Theorem))));
}
