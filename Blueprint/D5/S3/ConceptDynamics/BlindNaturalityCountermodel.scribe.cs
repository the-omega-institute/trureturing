using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class BlindNaturalityCountermodelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constant readout can commute with a process while losing target distinctions.",
        H("Blind Naturality Countermodel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("blind-naturality-countermodel"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/BlindNaturalityCountermodel."
                        + "blind_naturality_counterexample"),
                H("A commuting constant readout need not preserve target distinctions"),
                StatementSource.FromAuthor(CountermodelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source definitions distinguish a commuting macro square from "
                            + "faithfulness to a target. The countermodel constructs a constant "
                            + "readout from Boolean states to a one-point coordinate, an identity "
                            + "process, and a nonconstant Boolean target.")),
                    Paragraph(Text(
                        "The first public clause exhibits the induced one-point process making the "
                            + "square commute. The second states that the target does not factor "
                            + "through the constant readout, proved by the two Boolean states.")),
                    Paragraph(Text(
                        "Canonical Concept and Refines definitions are imported from the existing "
                            + "ConceptDynamics family. Searches found no exact countermodel theorem."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
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

    private static Formula CountermodelFormula()
    {
        Formula readout = F.Id("C");
        Formula process = F.Id("F");
        Formula target = F.Id("K");
        Formula induced = F.Id("Fbar");
        Formula boolType = F.Id("Bool");
        Formula unitType = F.Id("Unit");
        Formula composition = Seq(Operatorname, Grp(F.Id("circ")));
        Formula commuting = Seq(
            Exists, Sp, induced, Colon, Sp, Arrow(unitType, unitType), Comma, Sp,
            Seq(readout, Sp, composition, Sp, process), Sp, Eq, Sp,
            Seq(induced, Sp, composition, Sp, readout));
        Formula nonFaithful = Seq(
            Neg, Sp, Call("Refines", target, readout));

        return Disp(Seq(
            Exists, Sp, readout, Colon, Sp,
            Arrow(boolType, unitType), Comma, Sp,
            process, Colon, Sp, Arrow(boolType, boolType), Comma, Sp,
            target, Colon, Sp, Arrow(boolType, boolType), Comma, Esc,
            Open, Open, commuting, Close, Sp, Land, Sp, nonFaithful, Close, Dot));
    }
}
