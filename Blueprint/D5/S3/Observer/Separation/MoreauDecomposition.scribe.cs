using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class MoreauDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every vector has a unique orthogonal decomposition across a closed convex cone and its polar.",
        H("Moreau Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("closed-convex-cone-moreau-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/MoreauDecomposition.moreau_decomposition"),
                H("Closed convex cones admit a unique Moreau decomposition"),
                StatementSource.FromAuthor(MoreauFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C be a closed convex cone in a complete real inner-product space. "
                            + "Every vector x decomposes uniquely as x = p + r, where p belongs "
                            + "to C, r belongs to the polar cone, and p is orthogonal to r.")),
                    Paragraph(Text(
                        "Mathlib defines the inner dual using nonnegative pairings. Accordingly, "
                            + "polar membership of r is represented by membership of minus r in "
                            + "the inner dual of C; this is exactly the nonpositive-pairing "
                            + "convention for the polar cone.")),
                    Paragraph(Text(
                        "Existence uses the Hilbert projection theorem and its variational "
                            + "characterization. Testing the variational inequality at zero, "
                            + "twice the projection, and a translated cone point proves "
                            + "orthogonality and polar membership.")),
                    Paragraph(Text(
                        "For uniqueness, compare two admissible decompositions. The two polar "
                            + "inequalities make the self-inner-product of the difference of "
                            + "their cone components nonpositive; positivity forces that "
                            + "difference to vanish, and the residual components then agree.")),
                    Paragraph(Text(
                        "Repository search found the existing cone residual witness but no full "
                            + "existence-and-uniqueness declaration. Pinned Mathlib and Loogle "
                            + "supplied the projection existence and variational lemmas; a Loogle "
                            + "name query for Moreau returned zero declarations."))),
                DescribeRole.Theorem))));

    private static Formula MoreauFormula()
    {
        Formula space = F.Id("E");
        Formula cone = F.Id("C");
        Formula x = F.Id("x");
        Formula p = F.Id("p");
        Formula r = F.Id("r");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula dualCone = Seq(
            Operatorname, Grp(F.Id("InnerDual")), Open, cone, Close);
        Formula inner = Seq(Langle, Sp, p, Comma, Sp, r, Sp, Rangle);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, space, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open,
            space, Close, CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("InnerProductSpace")), Open,
            real, Comma, Sp, space, Close, CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("CompleteSpace")), Open,
            space, Close, CloseBracket, Comma, RowBreak,
            cone, Colon, Sp, Operatorname, Grp(F.Id("ProperCone")), Open,
            real, Comma, Sp, space, Close, Comma, Sp,
            x, Colon, Sp, space, Comma, RowBreak,
            Exists, Bang, Sp, p, Comma, Sp, r, Colon, Sp, space, Comma, RowBreak,
            p, Sp, InMacro, Sp, cone, Sp, Land, Sp,
            Minus, r, Sp, InMacro, Sp, dualCone, Sp, Land, Sp, RowBreak,
            inner, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            x, Sp, Eq, Sp, p, Sp, Plus, Sp, r, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
