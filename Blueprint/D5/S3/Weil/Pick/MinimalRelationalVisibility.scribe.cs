using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class MinimalRelationalVisibilityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/Pick/MinimalRelationalVisibility.minimal_relational_visibility";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two nonnegative Pick-kernel diagonal values can form an indefinite two-point relation.",
        H("Minimal Relational Visibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimal-relational-visibility"),
                DeclarationHandle.Create(Declaration),
                H("The first negative relation certificate has width two"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let s be a complex Schur candidate and a an interior disk point, "
                            + "with s zero at the origin and one at a. The displayed kernel, "
                            + "point family, and relation matrix are the source constructions.")),
                    Paragraph(Text(
                        "Both one-point diagonal tests are nonnegative. Sampling the two names "
                            + "together gives the matrix with rows (1,1) and (1,0), whose "
                            + "determinant is minus one and which is not positive semidefinite.")),
                    Paragraph(Text(
                        "Every conjugate-transpose product is positive semidefinite, so the same "
                            + "certificate rules out a Gram factorization of the joint relation."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula schur = F.Id("s");
        Formula point = F.Id("a");
        Formula z = F.Id("z");
        Formula w = F.Id("w");
        Formula index = F.Id("i");
        Formula kernel = F.Id("K");
        Formula points = F.Id("p");
        Formula relation = F.Id("R");
        Formula factor = F.Id("A");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula disk = Seq(Mathbb, Grp(F.Id("D")));
        Formula twoIndices = Seq(OpenBrace, D(0), Comma, Sp, D(1), CloseBrace);
        Formula matrices = Call("Matrix", D(2), D(2), complex);

        Formula kernelBody = new Formula.Fraction(
            Seq(D(1), Sp, Minus, Sp,
                Call("s", z), Sp, Times, Sp, Conjugate(Call("s", w))),
            Seq(D(1), Sp, Minus, Sp, z, Sp, Times, Sp, Conjugate(w)));
        Formula kernelDefinition = Seq(
            Open, z, Comma, Sp, w, Sp, Mapsto, Sp, kernelBody, Close);
        Formula relationDefinition = Seq(
            Open, index, Comma, Sp, F.Id("j"), Sp, Mapsto, Sp,
            Call("K", Call("p", index), Call("p", F.Id("j"))), Close);

        return Disp(Seq(
            Forall, Sp, schur, Colon, Sp, complex, Sp, To, Sp, complex, Comma, Sp,
            point, Sp, InMacro, Sp, disk, Comma, Sp,
            Open, Call("s", D(0)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Call("s", point), Sp, Eq, Sp, D(1), Close, Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("let")), Open,
            kernel, Sp, Colon, Eq, Sp, kernelDefinition, Comma, Sp,
            points, Sp, Colon, Eq, Sp, Call("vector", D(0), point), Comma, Sp,
            relation, Sp, Colon, Eq, Sp, relationDefinition, Close, SemiSpace,
            relation, Sp, Eq, Sp, Call("matrix", D(1), D(1), D(1), D(0)), Sp, Land, Sp,
            Open, Forall, Sp, index, Sp, InMacro, Sp, twoIndices, Comma, Sp,
            D(0), Sp, Leq, Sp, Call("R", index, index), Close, Sp, Land, Sp,
            Call("det", relation), Sp, Eq, Sp, Minus, D(1), Sp, Land, Sp,
            Neg, Call("PosSemidef", relation), Sp, Land, Sp,
            Neg, Exists, Sp, factor, Colon, Sp, matrices, Comma, Sp,
            relation, Sp, Eq, Sp, Call("conjTranspose", factor), Sp, Times, Sp, factor,
            Dot));
    }

    private static Formula Conjugate(Formula value) => Seq(Overline, Grp(value));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
