using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class GramNonzeroSpectrumMultiplicityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/LinearMemory/GramNonzeroSpectrumMultiplicity."
            + "gram_nonzero_spectrum_with_algebraic_multiplicity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rectangular adjoint Gram matrices have identical nonzero spectra with algebraic multiplicity.",
        H("Nonzero Gram Spectrum and Multiplicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("gram-nonzero-spectrum-with-algebraic-multiplicity"),
            DeclarationHandle.Create(Declaration),
            H("The nonzero Gram spectra agree with multiplicity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The rectangular characteristic-polynomial identity differs only by powers "
                    + "of the polynomial variable. At a nonzero scalar those factors have "
                    + "zero root multiplicity, leaving both root membership and algebraic "
                    + "multiplicity unchanged between the two adjoint Gram products."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula rows = F.Id("m");
        Formula columns = F.Id("n");
        Formula matrix = F.Id("M");
        Formula lambda = F.Id("lambda");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula matrixType = Call("Matrix", rows, columns, scalar);
        Formula adjoint = Call("conjTranspose", matrix);
        Formula stateGram = Call("mul", adjoint, matrix);
        Formula protocolGram = Call("mul", matrix, adjoint);
        Formula statePolynomial = Call("charpoly", stateGram);
        Formula protocolPolynomial = Call("charpoly", protocolGram);
        Formula sameRoot = Seq(
            Call("IsRoot", statePolynomial, lambda), Sp, Iff, Sp,
            Call("IsRoot", protocolPolynomial, lambda));
        Formula sameMultiplicity = Seq(
            Call("rootMultiplicity", lambda, statePolynomial), Sp, Eq, Sp,
            Call("rootMultiplicity", lambda, protocolPolynomial));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(scalar, Comma, Sp, rows, Comma, Sp, columns), type),
                Comma),
            Seq(
                Grp(), Typeclass("RCLike", scalar), Comma, Sp,
                Typeclass("Fintype", rows), Comma, Sp,
                Typeclass("DecidableEq", rows), Comma),
            Seq(
                Grp(), Typeclass("Fintype", columns), Comma, Sp,
                Typeclass("DecidableEq", columns), Comma),
            Seq(
                Forall, Sp, Typed(matrix, matrixType), Comma, Sp,
                Typed(lambda, scalar), Comma),
            Seq(
                Grp(), lambda, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                Open, sameRoot, Close, Sp, Land),
            Seq(
                Grp(), Open, sameMultiplicity, Close, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

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
}
