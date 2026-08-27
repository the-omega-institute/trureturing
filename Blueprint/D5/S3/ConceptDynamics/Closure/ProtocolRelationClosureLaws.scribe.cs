using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Closure;

internal sealed class ProtocolRelationClosureLawsDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Closure/ProtocolRelationClosureLaws."
            + "protocol_relation_closure_laws";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical protocol and relation closures satisfy all three closure laws.",
        H("Protocol and Relation Closure Laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("protocol-relation-closure-laws"),
                DeclarationHandle.Create(Declaration),
                H("Both canonical closures are extensive, monotone, and idempotent"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "DefinitionClosure is the repository's canonical protocol-family "
                            + "closure. The relation closure is constructed directly as the "
                            + "joint kernel of all RelationInvariantReadouts.")),
                    Paragraph(Text(
                        "The public statement carries three protocol-side clauses followed by "
                            + "the corresponding three relation-side clauses: extensivity, "
                            + "monotonicity, and idempotence.")),
                    Paragraph(Text(
                        "No new closure object is declared. The protocol laws reuse the frozen "
                            + "family theorem, while the relation laws follow from the canonical "
                            + "Galois primitives."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois"))]));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula EqualFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);

    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = And(clauses[index], result);
        }
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula sources = F.Id("Q");
        Formula larger = F.Id("Q2");
        Formula relation = F.Id("R");
        Formula largerRelation = F.Id("R2");
        Formula readout = F.Id("f");
        Formula conceptFamily = Call("Set", Call("Concept", state, output));
        Formula relationFamily = Call("Set", Seq(state, Sp, Times, Sp, state));
        Formula sourceClosure = Call("DefinitionClosure", sources);
        Formula largerClosure = Call("DefinitionClosure", larger);

        Formula RelationClosure(Formula input)
        {
            Formula invariantReadout = Call(
                "RelationInvariantReadouts", output, input);
            Formula family = Seq(
                LambdaLower, Sp, readout, Colon, Sp, invariantReadout,
                Comma, Sp, Call("val", readout));
            return Call("jointKernel", family);
        }

        Formula closedRelation = RelationClosure(relation);
        Formula closedLargerRelation = RelationClosure(largerRelation);

        Formula clauses = Conjoin(
            SubsetOf(sources, sourceClosure),
            Implies(SubsetOf(sources, larger), SubsetOf(sourceClosure, largerClosure)),
            EqualFormula(Call("DefinitionClosure", sourceClosure), sourceClosure),
            SubsetOf(relation, closedRelation),
            Implies(
                SubsetOf(relation, largerRelation),
                SubsetOf(closedRelation, closedLargerRelation)),
            EqualFormula(RelationClosure(closedRelation), closedRelation));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("O", type),
                Bound("Q", conceptFamily),
                Bound("Q2", conceptFamily),
                Bound("R", relationFamily),
                Bound("R2", relationFamily),
            ],
            clauses));
    }
}
