using System;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FlatCandidateAcyclicityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FlatCandidateAcyclicity.flat_candidate_cycle_exclusion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive shared lengths forbid directed cycles among flat-candidate dependencies.",
        H("The flat-candidate dependency graph is acyclic"),
        Blocks(
            Paragraph(Text("Let Q be a type of globally shared opposite-edge labels. A candidate relation C(a,b,c) records that a flat candidate with distinguished pair a has the two other opposite pairs b and c. The directed edge relation sends a to both b and c.")),
            Paragraph(Text("Assume every label has a positive generalized length z, in the stronger form 1<z(a), and every candidate satisfies z(a) >= 1+z(b)+z(c). Then no nonempty transitive directed path can return to its starting label. Each edge strictly decreases z, so a return path would give z(a)<z(a). The conclusion is independent of volume maximality and keeps repeated labels as separate edge occurrences.")),
            Describe.Lean(
                DescribeId.Create("flat-candidate-cycle-exclusion"),
                DeclarationHandle.Create(Declaration),
                H("Flat-candidate cycle exclusion"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof first derives strict decrease along every directed edge from the positive summand 1+z(c), then composes the decrease along Relation.TransGen and closes the cycle by irreflexivity of < on the reals."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        var q = F.Id("Q");
        var real = F.Id("Real");
        var z = F.Id("z");
        var c = F.Id("C");
        var a = F.Id("a");
        var b = F.Id("b");
        var d = F.Id("c");
        var one = F.D(1);
        var positivity = All("a", q, new Formula.Relation(one, FormulaRelationOperator.LessThan, Call("z", a)));
        var pgBody = Imp(
            Call("C", a, b, d),
            new Formula.Relation(
                Call("z", a),
                FormulaRelationOperator.GreaterThanOrEqual,
                Add(one, Add(Call("z", b), Call("z", d)))));
        var pg = All("a", q, All("b", q, All("c", q, pgBody)));
        var edge = Call("candidateEdge", c);
        var assumptions = And(positivity, pg);
        return All("Q", F.Id("Type"),
            All("z", Call("Function", q, real),
                All("C", Call("Function", q, Call("Function", q, Call("Function", q, F.Id("Prop")))),
                    Imp(assumptions, Neg(Call("HasDirectedCycle", edge))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Neg(Formula value) =>
        new Formula.Negate(value);
}
