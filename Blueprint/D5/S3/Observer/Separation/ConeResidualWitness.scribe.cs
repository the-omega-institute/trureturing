using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class ConeResidualWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closed convex cone residual gives its canonical separating dual witness.",
        H("Cone Residual Dual Witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-cone-residual-is-a-dual-witness"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/ConeResidualWitness."
                        + "cone_residual_observer_duality"),
                H("The cone residual is a dual witness"),
                StatementSource.FromAuthor(ConeResidualWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C be a closed convex cone in an arbitrary real Hilbert space, let p "
                            + "be a nearest point of x in C, set r = x - p, and set w = -r. Then w "
                            + "belongs to the inner dual cone. If x is outside C, w is nonnegative "
                            + "on every point of C while its value on x is exactly minus the squared "
                            + "norm of r and is strictly negative.")),
                    Paragraph(Text(
                        "The metric-projection variational inequality is applied at zero, twice p, "
                            + "and c + p. These three tests respectively give the two inequalities "
                            + "forcing orthogonality and the polar inequality for every c in C. "
                            + "The strict sign follows because a zero residual would put x in C.")),
                    Paragraph(Text(
                        "Repository searches found no existing residual-duality declaration. Pinned "
                            + "Mathlib supplies the inner-dual definition, the Hilbert projection "
                            + "theorem, and the variational characterization used directly in the "
                            + "proof. Loogle confirmed those declarations and found no exact wrapper; "
                            + "LeanSearch returned only general cone infrastructure."))),
                DescribeRole.Theorem))));

    private static Formula ConeResidualWitnessFormula()
    {
        Formula space = F.Id("E");
        Formula cone = F.Id("C");
        Formula x = F.Id("x");
        Formula p = F.Id("p");
        Formula r = F.Id("r");
        Formula w = F.Id("w");
        Formula c = F.Id("c");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula projection = Seq(
            F.Id("P"), Underscore, Grp(cone), Open, x, Close);
        Formula innerWc = Seq(Langle, Sp, w, Comma, Sp, c, Sp, Rangle);
        Formula innerWx = Seq(Langle, Sp, w, Comma, Sp, x, Sp, Rangle);
        Formula residualNormSq = Seq(new Formula.Norm(r), Caret, Grp(D(2)));
        Formula dualCone = Seq(
            Operatorname, Grp(F.Id("InnerDual")), Open, cone, Close);

        return Disp(Seq(
            Forall, Sp, space, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open,
            space, Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("InnerProductSpace")), Open,
            real, Comma, Sp, space, Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("CompleteSpace")), Open,
            space, Close, CloseBracket, Comma, Esc,
            cone, Colon, Sp, Operatorname, Grp(F.Id("ProperCone")), Open,
            real, Comma, Sp, space, Close, Comma, Esc,
            x, Colon, Sp, space, Comma, Quad, Sp,
            Operatorname, Grp(F.Id("let")), Open,
            p, Sp, Eq, Sp, projection, Comma, Sp,
            r, Sp, Eq, Sp, x, Sp, Minus, Sp, p, Comma, Sp,
            w, Sp, Eq, Sp, Minus, r, Close, Semi, Quad, Sp,
            w, Sp, InMacro, Sp, dualCone, Sp, Land, Sp,
            Open, Neg, Sp, Open, x, Sp, InMacro, Sp, cone, Close,
            Sp, Rightarrow, Sp,
            Open,
            Open, Forall, Sp, c, Colon, Sp, space, Comma, Esc,
            c, Sp, InMacro, Sp, cone, Sp, Rightarrow, Sp,
            D(0), Sp, Leq, Sp, innerWc, Close,
            Sp, Land, Sp,
            innerWx, Sp, Eq, Sp, Minus, residualNormSq,
            Sp, Land, Sp,
            innerWx, Sp, Lt, Sp, D(0),
            Close, Close, Dot));
    }
}
