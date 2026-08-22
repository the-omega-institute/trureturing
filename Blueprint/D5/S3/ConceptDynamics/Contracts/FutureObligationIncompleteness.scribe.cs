using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Contracts;

internal sealed class FutureObligationIncompletenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A noninjective interface misses a separating future Boolean obligation.",
        H("Future Obligation Incompleteness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("collision-obligation"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness."
                        + "collisionObligation"),
                H("Collision obligation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a distinguished current object, the collision obligation is the "
                        + "Boolean readout that accepts exactly objects equal to it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nonfaithful-interface-future-incomplete"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness."
                        + "nonfaithful_interface_future_incomplete"),
                H("A nonfaithful interface is incomplete for future obligations"),
                StatementSource.FromAuthor(IncompletenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The interface and every future Boolean obligation use the canonical "
                            + "concept-readout carrier. From noninjectivity, the pinned function "
                            + "theorem supplies distinct objects with the same interface value.")),
                    Paragraph(Text(
                        "The public forward implication names the collision objects, states their "
                            + "interface equality, exposes separation by the collision obligation, "
                            + "and states directly that no Boolean factor through the interface "
                            + "recovers that obligation.")),
                    Paragraph(Text(
                        "The independent reverse implication assumes factorization of every Boolean "
                            + "obligation and concludes injectivity. Its premise is local to that "
                            + "implication and is not assumed by the forward half.")),
                    Paragraph(Text(
                        "The existing disclosure-defect theorem is applied to the explicit collision "
                            + "and separating obligation in both proof branches."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Rewriting/Quotients/InformedDisclosureDefect")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/ConceptFiberDecomposition")),
        ]));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula IncompletenessFormula()
    {
        Formula xType = F.Id("X");
        Formula interfaceType = F.Id("B");
        Formula interfaceMap = F.Id("V");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula obligation = F.Id("O");
        Formula factor = F.Id("factor");
        Formula boolType = F.Id("Bool");
        Formula collisionAtX = Call("collisionObligation", x);
        Formula separates = Seq(
            Apply(collisionAtX, x), Sp, Neq, Sp, Apply(collisionAtX, y));
        Formula nonfactorization = Seq(
            Neg, Sp, Open, Exists, Sp, factor, Colon, Sp,
            Arrow(interfaceType, boolType), Comma, Sp,
            collisionAtX, Sp, Eq, Sp, factor, Sp, Circ, Sp, interfaceMap, Close);
        Formula forward = Seq(
            Neg, Sp, Call("Injective", interfaceMap), Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, x, Comma, Sp, y, Colon, Sp, xType, Comma, RowBreak, Grp(),
            x, Sp, Neq, Sp, y, Sp, Land, Sp,
            Apply(interfaceMap, x), Sp, Eq, Sp, Apply(interfaceMap, y), Sp, Land,
            RowBreak, Grp(), separates, Sp, Land, Sp, nonfactorization);
        Formula complete = Seq(
            Forall, Sp, obligation, Colon, Sp, Call("Concept", xType, boolType), Comma, Sp,
            Exists, Sp, factor, Colon, Sp, Arrow(interfaceType, boolType), Comma, Sp,
            obligation, Sp, Eq, Sp, factor, Sp, Circ, Sp, interfaceMap);
        Formula reverse = Seq(
            Open, complete, Close, Sp, Rightarrow, Sp, Call("Injective", interfaceMap));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, xType, Comma, Sp, interfaceType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            interfaceMap, Colon, Sp, Call("Concept", xType, interfaceType), Comma, RowBreak, Grp(),
            Open, forward, Close, Sp, Land, RowBreak, Grp(),
            Open, reverse, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
