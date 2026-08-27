using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class HankelGramianSingularValuesDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/LinearMemory/HankelGramianSingularValues."
            + "hankel_gramian_singular_values";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive Hankel singular values are the square roots of the controllability-observability Gramian-product spectrum.",
        H("Hankel Gramian Singular Values"),
        Blocks(Describe.Lean(
            DescribeId.Create("hankel-gramian-singular-values"),
            DeclarationHandle.Create(Declaration),
            H("Hankel and Gramian-product spectra agree"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The Hankel map is constructed by composing the controllability root with future "
                    + "output. Self-adjointness identifies its adjoint-square with the displayed "
                    + "Gramian product; injectivity makes every indexed singular value positive."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula root = F.Id("S");
        Formula future = F.Id("O");
        Formula dimension = F.Id("n");
        Formula hankel = F.Id("H");
        Formula product = F.Id("P");
        Formula symmetry = F.Id("hP");
        Formula index = F.Id("i");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output,
            Colon, Sp, F.Id("Type"), Comma, Sp,
            root, Comma, Sp, future, Comma, Sp, dimension, Comma, RowBreak, Grp(),
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("NormedAddCommGroup", state), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, state), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, state), Comma, RowBreak, Grp(),
            Call("NormedAddCommGroup", output), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, output), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, output), Sp, Land, Sp,
            root, Sp, InMacro, Sp, Call("LinearMap", scalar, state, state), Sp, Land, Sp,
            future, Sp, InMacro, Sp, Call("LinearMap", scalar, state, output), Comma,
            RowBreak, Grp(),
            Call("adjoint", root), Sp, Eq, Sp, root, Sp, Land, Sp,
            Call("Injective", root), Sp, Land, Sp, Call("Injective", future), Sp, Land, Sp,
            dimension, Sp, InMacro, Sp, F.Id("N"), Sp, Land, Sp,
            Call("finrank", scalar, state), Sp, Eq, Sp, dimension, Sp, Rightarrow,
            RowBreak, Grp(),
            Call("let", hankel, Call("comp", future, root)), Comma, Sp,
            Call("let", product, Call("comp", root,
                Call("comp", Call("comp", Call("adjoint", future), future), root))), Comma,
            RowBreak, Grp(),
            Exists, Sp, symmetry, Colon, Sp, Call("IsSymmetric", product), Comma, Sp,
            Forall, Sp, index, Sp, InMacro, Sp, Call("Fin", dimension), Comma, Sp,
            D(0), Sp, Lt, Sp, Call("singularValue", hankel, index), Sp, Land, Sp,
            Call("singularValue", hankel, index), Sp, Eq, Sp,
            Call("sqrt", Call("eigenvalue", symmetry, dimension, index)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
