using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class PureWhiteInnovationDirectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite contact atoms leave explicit nonzero directions at the white spectral floor.",
        H("Pure White Innovation Directions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pure-white-innovation-directions-are-floor-eigenvectors"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/PureWhiteInnovationDirection."
                        + "pure_white_innovation_direction"),
                H("Contact-analysis kernel directions are white-floor eigenvectors"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The contact points are taken from the unitary subtype of the complex "
                            + "circle, and each contact weight is a strictly positive real. "
                            + "These source objects construct the weighted analysis matrix and "
                            + "the Toeplitz carrier with its scalar white floor.")),
                    Paragraph(Text(
                        "Every vector annihilated by the contact analysis is an eigenvector of "
                            + "the constructed Toeplitz matrix at the floor value omega. Thus "
                            + "the finite atomic update does not activate that direction.")),
                    Paragraph(Text(
                        "The strict inequality M < N plus one gives a nonzero analysis-kernel "
                            + "direction by rank-nullity. The public conclusion records both the "
                            + "kernel-to-eigenspace bridge and this nontriviality witness.")),
                    Paragraph(Text(
                        "The proof uses the adjoint-Gram positivity primitive and finite-dimensional "
                            + "rank-nullity; no arbitrary matrix or auxiliary definition is supplied."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula n = F.Id("N");
        Formula m = F.Id("M");
        Formula omega = F.Id("omega");
        Formula contact = F.Id("z");
        Formula weight = F.Id("q");
        Formula r = F.Id("r");
        Formula j = F.Id("j");
        Formula x = F.Id("x");
        Formula analysis = F.Id("A");
        Formula toeplitz = F.Id("T");
        Formula dimension = Seq(n, Plus, D(1));
        Formula contactAtR = Apply(contact, r);
        Formula weightAtR = Apply(weight, r);
        Formula contactPowerJ = Seq(contactAtR, Caret, Grp(j));
        Formula analysisEntry = Seq(
            Sqrt, Grp(weightAtR), Sp, Grp(contactPowerJ), Caret, Grp(Star));
        Formula matrixType = Call(
            "Matrix", Call("Fin", m), Call("Fin", dimension), complex);
        Formula vectorType = Arrow(Call("Fin", dimension), complex);
        Formula analysisDefinition = Seq(
            Typed(analysis, matrixType), Comma, Sp,
            Forall, Sp, Typed(r, Call("Fin", m)), Comma, Sp,
            Typed(j, Call("Fin", dimension)), Comma, Sp,
            Sub(analysis, Seq(r, Comma, j)), Sp, Eq, Sp, analysisEntry);
        Formula toeplitzDefinition = Seq(
            Typed(toeplitz, Call("Matrix", Call("Fin", dimension),
                Call("Fin", dimension), complex)), Sp, Eq, Sp,
            omega, F.Id("I"), Sp, Plus, Sp,
            analysis, Caret, Grp(Star), analysis);
        Formula kernel = Call("ker", analysis);
        Formula eigenspace = Call("eigenspace", toeplitz, omega);
        Formula kernelBridge = Seq(
            kernel, Sp, Eq, Sp, eigenspace);
        Formula nonzeroKernel = Seq(
            Exists, Sp, Typed(x, vectorType), Comma, Sp,
            x, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            x, Sp, InMacro, Sp, kernel);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(n, natural), Comma, Sp, Typed(m, natural), Comma, Sp,
                Typed(omega, real), Comma),
            Seq(
                Typed(contact, Arrow(Call("Fin", m), Call("unitary", complex))), Comma),
            Seq(
                Typed(weight, Arrow(Call("Fin", m),
                    Seq(OpenBrace, F.Id("x"), InMacro, Sp, real, Sp, Mid, Sp,
                        D(0), Sp, Lt, Sp, F.Id("x"), CloseBrace))), Comma),
            Seq(
                m, Sp, Lt, Sp, dimension, Sp, Rightarrow),
            Seq(
                Operatorname, Grp(F.Id("let")), Open,
                analysisDefinition, Comma, Sp, toeplitzDefinition, Close, SemiSpace),
            Seq(
                kernelBridge, Sp, Land),
            Seq(
                nonzeroKernel, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
