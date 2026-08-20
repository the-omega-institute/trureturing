using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class DiagonalInterfaceConjugacyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal-interface-preserving similarity exactly recovers finite map conjugacy.",
        H("Diagonal Interface Conjugacy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("diagonal-interface-similarity-is-map-conjugacy"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Dynamics/DiagonalInterfaceConjugacy."
                        + "diagonal_interface_conjugacy"),
                H("Diagonal-interface similarity is map conjugacy"),
                StatementSource.FromAuthor(ConjugacyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each finite state type, the transfer operator is constructed from "
                            + "the state map by sending every coordinate basis vector to the "
                            + "basis vector at its image. The diagonal interface is independently "
                            + "constructed as the full range of pointwise multiplication operators.")),
                    Paragraph(Text(
                        "A state equivalence transports coordinate functions and directly "
                            + "conjugates both constructions. Conversely, diagonal preservation "
                            + "makes each conjugated coordinate projection diagonal. Its nonzero "
                            + "coordinate reconstructs an injective state map, and finite dimension "
                            + "makes that map bijective.")),
                    Paragraph(Text(
                        "The imported diagonal-corner reconstruction theorem then turns transfer "
                            + "similarity into the pointwise conjugacy equation. Repository and "
                            + "pinned-Mathlib searches found the transport, finite-rank, and corner "
                            + "dependencies used by the proof, but no theorem packaging the full "
                            + "displayed equivalence."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Field(Formula owner, string name) =>
        Seq(owner, Dot, F.Id(name));

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula ConjugacyFormula()
    {
        Formula yType = F.Id("Y");
        Formula zType = F.Id("Z");
        Formula tau = F.Id("tau");
        Formula sigma = F.Id("sigma");
        Formula phi = F.Id("phi");
        Formula y = F.Id("y");
        Formula u = F.Id("U");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula sourceSpace = Apply(Seq(Operatorname, Grp(F.Id("Finsupp"))), yType, complex);
        Formula targetSpace = Apply(Seq(Operatorname, Grp(F.Id("Finsupp"))), zType, complex);
        Formula sourceTransfer = Apply(F.Id("transferOperator"), tau);
        Formula targetTransfer = Apply(F.Id("transferOperator"), sigma);
        Formula conjugate = Field(u, "conj");
        Formula sourceDiagonal = Apply(F.Id("diagonalInterface"), yType);
        Formula targetDiagonal = Apply(F.Id("diagonalInterface"), zType);

        return Disp(Seq(
            Forall, Sp, yType, Comma, Sp, zType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Typeclass("Finite", yType), Comma, Sp,
            Typeclass("Finite", zType), Comma, Esc,
            tau, Colon, Sp, yType, Sp, To, Sp, yType, Comma, Sp,
            sigma, Colon, Sp, zType, Sp, To, Sp, zType, Comma, RowBreak,
            Open, Exists, Sp, phi, Colon, Sp,
            Apply(Seq(Operatorname, Grp(F.Id("Equiv"))), yType, zType), Comma, Sp,
            Forall, Sp, y, Comma, Sp,
            Apply(phi, Apply(tau, y)), Sp, Eq, Sp, Apply(sigma, Apply(phi, y)), Close,
            Sp, Iff, Sp, RowBreak,
            Exists, Sp, u, Colon, Sp,
            Apply(Seq(Operatorname, Grp(F.Id("LinearEquiv"))),
                complex, sourceSpace, targetSpace), Comma, Esc,
            Apply(conjugate, sourceTransfer), Sp, Eq, Sp, targetTransfer, Sp, Land, RowBreak,
            Apply(Seq(Operatorname, Grp(F.Id("image"))), conjugate, sourceDiagonal),
            Sp, Eq, Sp, targetDiagonal, Dot));
    }
}
