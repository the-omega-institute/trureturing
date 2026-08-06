using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class TwelveScaleReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Depth/TwelveScaleReduction",
                "Record partial arithmetic progress toward the unresolved source floor reduction."),
            H("Twelve-Scale Reduction"),
            Blocks(
                Paragraph(Text(
                    "This module records four partial arithmetic lemmas toward the unresolved source floor reduction. It does not identify the rational parameter with the largest partial quotient, does not supply the 2958-case or minimum-attainment certificates, does not identify the moat, envelope, or diffusion readings with the normalized finite-sample minimum, and does not reconstruct the historical sampling configuration or its leakage.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("normalized-twelve-lower-bound"),
                    H("Nonzero multiples of twelve obey the normalized floor"),
                    LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.twelve_scale_le_normalized_magnitude"),
                    Disp(Seq(Forall, Sp, Psi, InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, Forall, Sp, F.Id("A"), InMacro, Mathbb, Grp(F.Id("Q")), Underscore, Grp(Gt, D(0)), Comma, Esc, Open, D(1, 2), Mid, Psi, Sp, Land, Sp, Psi, Neq, D(0), Close, Sp, Rightarrow, Sp, Frac, Grp(D(1, 2)), Grp(F.Id("A")), Leq, Frac, Grp(Bar, Psi, Bar), Grp(F.Id("A")))),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "A nonzero integer divisible by twelve has absolute value at least twelve. Dividing by a positive rational parameter preserves the inequality; no orbit or maximum-partial-quotient interpretation is inferred.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("normalized-twelve-equality"),
                    H("The normalized floor equality detects absolute value twelve"),
                    LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.normalized_magnitude_eq_twelve_scale_iff"),
                    Disp(Seq(Forall, Sp, Psi, InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, Forall, Sp, F.Id("A"), InMacro, Mathbb, Grp(F.Id("Q")), Underscore, Grp(Gt, D(0)), Comma, Esc, Frac, Grp(Bar, Psi, Bar), Grp(F.Id("A")), Eq, Frac, Grp(D(1, 2)), Grp(F.Id("A")), Leftrightarrow, Bar, Psi, Bar, Eq, D(1, 2))),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a positive denominator, cancellation shows that the normalized magnitude equals twelve over that denominator exactly when the integer magnitude is twelve. The theorem does not produce such a sample member.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("finite-sample-twelve-minimum"),
                    H("A witnessed finite sample has exact twelve-scale minimum"),
                    LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.twelve_scale_is_normalized_sample_minimum"),
                    Disp(Seq(Forall, Sp, F.Id("S"), Subset, Underscore, Grp(Mathrm, Grp(F.Id("fin"))), Mathbb, Grp(F.Id("Z")), Comma, Esc, Forall, Sp, F.Id("A"), InMacro, Mathbb, Grp(F.Id("Q")), Underscore, Grp(Gt, D(0)), Comma, Esc, Open, Open, Forall, Psi, InMacro, Sp, F.Id("S"), Comma, Esc, D(1, 2), Mid, Psi, Land, Psi, Neq, D(0), Close, Land, Open, Exists, Psi, Underscore, D(0), InMacro, Sp, F.Id("S"), Comma, Esc, Bar, Psi, Underscore, D(0), Bar, Eq, D(1, 2), Close, Close, Rightarrow, Sp, Min, Left, OpenBrace, Frac, Grp(Bar, Psi, Bar), Grp(F.Id("A")), Colon, Psi, InMacro, Sp, F.Id("S"), Right, CloseBrace, Eq, Frac, Grp(D(1, 2)), Grp(F.Id("A")))),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If every member of a finite integer sample is a nonzero multiple of twelve and one supplied member has magnitude twelve, then twelve over the positive parameter is a member and lower bound of the normalized sample. The enumeration and witness remain explicit premises.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("finite-sample-minimum-uniqueness"),
                    H("A normalized finite-sample minimum is unique"),
                    LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.normalized_sample_minimum_unique"),
                    Disp(Seq(Forall, Sp, F.Id("x"), Comma, F.Id("y"), InMacro, Sp, F.Id("N"), Underscore, F.Id("A"), Open, F.Id("S"), Close, Comma, Esc, Open, Open, Forall, Sp, F.Id("z"), InMacro, Sp, F.Id("N"), Underscore, F.Id("A"), Open, F.Id("S"), Close, Comma, Esc, F.Id("x"), Leq, Sp, F.Id("z"), Close, Land, Open, Forall, Sp, F.Id("z"), InMacro, Sp, F.Id("N"), Underscore, F.Id("A"), Open, F.Id("S"), Close, Comma, Esc, F.Id("y"), Leq, Sp, F.Id("z"), Close, Close, Rightarrow, Sp, F.Id("x"), Eq, F.Id("y"))),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Two normalized sample members that are each no greater than every member are equal by antisymmetry. This order-theoretic uniqueness does not identify any other statistical reading with the sample minimum.")))
                )),
[
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Depth/TwelveScaleReduction.normalized_magnitude_eq_twelve_scale_iff")),
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Depth/TwelveScaleReduction.normalized_sample_minimum_unique")),
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Depth/TwelveScaleReduction.twelve_scale_is_normalized_sample_minimum")),
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Depth/TwelveScaleReduction.twelve_scale_le_normalized_magnitude")),
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S1/Phase/SeatTowerArithmetic")),
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S1/Phase/ZeroOrbitCongruence")),
                    ]));
}
