using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class ToeplitzFlatFloorMultiplicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A contact Gram update has floor omega with the predicted multiplicity.",
        H("Toeplitz Flat-Floor Multiplicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("toeplitz-flat-floor-multiplicity"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/ToeplitzFlatFloorMultiplicity."
                        + "toeplitz_flat_floor_multiplicity"),
                H("Finite contact rank leaves an exact flat spectral floor"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The contact points live directly in the unitary subtype of the complex "
                            + "unit circle, and every weight lives in the strictly positive real "
                            + "subtype. The weighted analysis matrix is constructed from their "
                            + "contact vectors rather than supplied as an arbitrary matrix.")),
                    Paragraph(Text(
                        "The first public clause expands the constructed adjoint Gram matrix "
                            + "entry by entry, exposing the scalar white floor and the positive "
                            + "finite contact update on the exact complex Toeplitz carrier.")),
                    Paragraph(Text(
                        "Adjoint Gram positivity places every real spectral value above omega. "
                            + "Rank-nullity leaves at least N plus one minus M independent kernel "
                            + "directions, and each becomes an omega eigenvector after the scalar "
                            + "floor is added.")),
                    Paragraph(Text(
                        "The conclusion states the minimum as an IsLeast property of the real "
                            + "spectrum and states the multiplicity as the complex dimension of "
                            + "the omega eigenspace. Hermitian spectral theory identifies this "
                            + "geometric multiplicity with eigenvalue multiplicity."))),
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
        Formula k = F.Id("k");
        Formula analysis = F.Id("A");
        Formula toeplitz = F.Id("T");
        Formula dimension = Seq(n, Plus, D(1));
        Formula contactAtR = Apply(contact, r);
        Formula weightAtR = Apply(weight, r);
        Formula contactPowerJ = Seq(contactAtR, Caret, Grp(j));
        Formula contactPowerKStar = Seq(
            Grp(contactAtR, Caret, Grp(k)), Caret, Grp(Star));
        Formula analysisEntry = Seq(
            Sqrt, Grp(weightAtR), Sp, Grp(contactPowerJ), Caret, Grp(Star));
        Formula matrixType = Call(
            "Matrix", Call("Fin", m), Call("Fin", dimension), complex);
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
        Formula floorEntry = Seq(
            Sub(F.Id("delta"), Seq(j, k)), omega);
        Formula residualEntry = Seq(
            Sum, Underscore, Grp(r, Eq, D(1)), Caret, Grp(m), Sp,
            weightAtR, Sp, contactPowerJ, Sp, contactPowerKStar);
        Formula entryIdentity = Seq(
            Forall, Sp, Typed(j, Call("Fin", dimension)), Comma, Sp,
            Typed(k, Call("Fin", dimension)), Comma, Sp,
            Sub(toeplitz, Seq(j, k)), Sp, Eq, Sp,
            floorEntry, Sp, Plus, Sp, residualEntry);
        Formula realSpectrum = Call("spectrum", real, toeplitz);
        Formula multiplicity = Call(
            "finrank", complex, Call("eigenspace", toeplitz, omega));

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
                Open, entryIdentity, Close, Sp, Land),
            Seq(
                Call("IsLeast", realSpectrum, omega), Sp, Land),
            Seq(
                dimension, Sp, Minus, Sp, m, Sp, Leq, Sp, multiplicity, Dot),
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
