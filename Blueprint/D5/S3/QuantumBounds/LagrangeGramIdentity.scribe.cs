using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class LagrangeGramIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The Cauchy-Schwarz defect equals a manifestly nonnegative sum of squares (the coordinate Gram remainder).",
        H("Lagrange-Gram Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lagrange-gram-identity"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity"),
                H("The Cauchy-Schwarz defect is a sum of squares"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Sum, Underscore, Grp(F.Id("i")), Sp, F.Id("u"), Underscore, Grp(F.Id("i")), Caret, Grp(D(2)), Close,
                    Open, Sum, Underscore, Grp(F.Id("i")), Sp, F.Id("v"), Underscore, Grp(F.Id("i")), Caret, Grp(D(2)), Close,
                    Minus, Open, Sum, Underscore, Grp(F.Id("i")), Sp, F.Id("u"), Underscore, Grp(F.Id("i")), F.Id("v"), Underscore, Grp(F.Id("i")), Close, Caret, Grp(D(2)),
                    Eq, Frac, Grp(D(1)), Grp(D(2)), Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp, Sum, Underscore, Grp(F.Id("j")), Sp,
                    Open, F.Id("u"), Underscore, Grp(F.Id("i")), F.Id("v"), Underscore, Grp(F.Id("j")), Minus, F.Id("u"), Underscore, Grp(F.Id("j")), F.Id("v"), Underscore, Grp(F.Id("i")), Close, Caret, Grp(D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real families u and v indexed by a finite set, the Cauchy-Schwarz defect "
                        + "(sum of u_i^2)(sum of v_i^2) - (sum of u_i v_i)^2 equals one half of the double sum "
                        + "over i and j of (u_i v_j - u_j v_i)^2. The right-hand side is a sum of squares, hence "
                        + "nonnegative, which is exactly the Cauchy-Schwarz inequality; it is the coordinate form "
                        + "of the Gram wedge-remainder G in the identity ||u||^2 ||v||^2 = |<u,v>|^2 + G.")),
                    Paragraph(Text(
                        "The theorem establishes only this algebraic sum-of-squares identity; it does not "
                        + "instantiate the Cramer-Rao, Robertson-Schrodinger, or quantum Cramer-Rao specialisations "
                        + "of the note, which require the corresponding inner-product structures."))),
                DescribeRole.Theorem))));
}
