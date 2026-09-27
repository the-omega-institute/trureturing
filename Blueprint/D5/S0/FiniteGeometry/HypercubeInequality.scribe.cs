using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.FiniteGeometry;

internal sealed class HypercubeInequalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S0/FiniteGeometry/HypercubeInequality";
    private static LibraryNoteRef SourceNote => LibraryNoteRef.Create(
        "D5/L/averkovvondichtersoprunov2026logsubmodularity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant-defined Hypercube Inequality holds in every positive dimension.",
        H("The All-Dimensional Hypercube Inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("augmented-cube-matrix"),
                DeclarationHandle.Create(Module + ".augmentedCube"),
                H("The augmented cube matrix"),
                StatementSource.FromAuthor(AugmentedCubeFormula()),
                AssessedProvenance.FromLiterature(SourceNote),
                Blocks(Paragraph(Text(
                    "The columns are indexed by Boolean cube vertices. The first d rows "
                        + "are the vertex coordinates, cast to integers, and the final row "
                        + "is one. Thus every maximal minor is the oriented normalized "
                        + "volume of its unordered (d+1)-vertex subset."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hypercube-determinant-weight"),
                DeclarationHandle.Create(Module + ".hypercubeWeight"),
                H("The weighted normalized-volume sum"),
                StatementSource.FromAuthor(WeightFormula()),
                AssessedProvenance.FromLiterature(SourceNote),
                Blocks(Paragraph(Text(
                    "The sum ranges once over every finite subset of cube vertices with "
                        + "cardinality d+1. Its coefficient is the absolute integer "
                        + "determinant of the actual augmented columns, multiplied by the "
                        + "weights on the subset. There is no ordering multiplicity and no "
                        + "factorial normalization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("all-dimensional-hypercube-inequality"),
                DeclarationHandle.Create(Module + ".result"),
                H("Equation (16) in every positive dimension"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(SourceNote),
                Blocks(
                    Paragraph(Text(
                        "For every d at least one and every nonnegative real weight on the "
                            + "Boolean cube, the determinant-weighted sum times the total "
                            + "weight to the power d-1 is bounded by the product of the two "
                            + "opposite facet sums in every coordinate.")),
                    Paragraph(Text(
                        "The proof first expands the weighted Gram determinant by maximal "
                            + "minors using the characteristic-polynomial minor formula and "
                            + "det(1+PQ)=det(1+QP). Integer determinants satisfy |det| <= "
                            + "|det|^2, so the source weight is bounded by this positive "
                            + "semidefinite determinant.")),
                    Paragraph(Text(
                        "If the total weight is zero, nonnegativity makes every weight and "
                            + "both sides zero. Otherwise the final scalar block is positive. "
                            + "Its Schur complement, scaled by the total weight, is positive "
                            + "semidefinite and has diagonal entries equal to the products "
                            + "of the two exact coordinate-facet sums. A Gram factorization "
                            + "and the orientation volume bound compare its determinant with "
                            + "the product of those diagonal entries. The Schur determinant "
                            + "identity supplies exactly the factor s^(d-1). Singular Gram "
                            + "matrices and zero facet sums require no division or positivity "
                            + "assumption beyond the separated total-zero case."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hypercube-inequality"),
                    ResolutionKind.Proved)))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula DVar => F.Id("d");
    private static Formula V => F.Id("v");
    private static Formula I => F.Id("i");
    private static Formula S => F.Id("S");
    private static Formula X => F.Id("x");
    private static Formula Cube => Seq(OpenBrace, D(0), Comma, D(1), CloseBrace,
        Caret, Grp(DVar));
    private static Formula FinD => Call("Fin", DVar);
    private static Formula Xv => new Formula.Subscript(X, V);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Indexed(Formula symbol, Formula condition, Formula body) =>
        Seq(new Formula.Subscript(symbol, condition), Sp, body);

    private static Formula Paren(Formula value) => Seq(Left, Open, value, Right, Close);

    private static Formula AugmentedCubeFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, DVar, Sp, InMacro, Sp, Naturals, Comma, Sp,
            Call("A", DVar), Colon, Sp,
            Paren(Seq(Paren(Seq(FinD, Sp, Plus, Sp, OpenBrace, Star, CloseBrace)),
                Sp, Times, Sp, Cube)), Sp, To, Sp, Integers, Comma),
        Seq(Call("A", DVar, Call("inl", I), V), Sp, Eq, Sp,
            new Formula.Subscript(V, I), Comma, Sp,
            Call("A", DVar, Call("inr", Star), V), Sp, Eq, Sp, D(1), Dot),
    ]));

    private static Formula WeightFormula()
    {
        Formula subsets = Seq(S, Sp, Subseteq, Sp, Cube, Comma, Sp,
            Call("card", S), Sp, Eq, Sp, DVar, Sp, Plus, Sp, D(1));
        Formula determinant = new Formula.Absolute(Call("det", Call("columns", Call("A", DVar), S)));
        Formula product = Indexed(Prod, Seq(V, Sp, InMacro, Sp, S), Xv);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, DVar, Sp, InMacro, Sp, Naturals, Comma, Sp,
                X, Colon, Sp, Cube, Sp, To, Sp, Reals, Comma),
            Seq(Call("W", DVar, X), Sp, Eq, Sp,
                Indexed(Sum, subsets, Seq(determinant, Sp, product)), Dot),
        ]));
    }

    private static Formula ResultFormula()
    {
        Formula nonnegative = Seq(Forall, Sp, V, Sp, InMacro, Sp, Cube, Comma, Sp,
            D(0), Sp, Leq, Sp, Xv);
        Formula total = Indexed(Sum, Seq(V, Sp, InMacro, Sp, Cube), Xv);
        Formula left = Seq(Call("W", DVar, X), Sp,
            new Formula.Power(Paren(total), Seq(DVar, Sp, Minus, Sp, D(1))));
        Formula facet0 = Indexed(Sum,
            Seq(V, Sp, InMacro, Sp, Cube, Comma, Sp,
                new Formula.Subscript(V, I), Sp, Eq, Sp, D(0)), Xv);
        Formula facet1 = Indexed(Sum,
            Seq(V, Sp, InMacro, Sp, Cube, Comma, Sp,
                new Formula.Subscript(V, I), Sp, Eq, Sp, D(1)), Xv);
        Formula right = Indexed(Prod, Seq(I, Sp, InMacro, Sp, FinD),
            Seq(Paren(facet0), Sp, Paren(facet1)));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, DVar, Sp, InMacro, Sp, Naturals, Comma, Sp,
                D(1), Sp, Leq, Sp, DVar, Comma),
            Seq(Forall, Sp, X, Colon, Sp, Cube, Sp, To, Sp, Reals, Comma, Sp,
                Paren(nonnegative), Sp, Implies),
            Seq(left, Sp, Leq, Sp, right, Dot),
        ]));
    }
}
