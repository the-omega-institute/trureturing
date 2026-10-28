using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class DemoStrongPeriodBoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/demo2026periodicity");
    private static readonly LibraryNoteRef FixedPoints =
        LibraryNoteRef.Create("D5/L/GraphInvariants/erickson2024metamour");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The connected singleton refutes the unrestricted strong distance-two period bound.",
        H("The strong distance-two period bound fails at the singleton"),
        Blocks(
            Paragraph(Text("The operator uses exact shortest distance two and keeps the same vertex type. Its iterates may be disconnected. Strong return means an isomorphism to the initial graph after a positive number of applications; it does not mean an eventual return or preservation of vertex labels. The three graph definitions are universe-polymorphic. The closed conjecture quantifies vertex types in Type, with a finite-type instance and connectedness as its only graph hypothesis.")),
            Describe.Lean(DescribeId.Create("demo-period-distance-two"),
                DeclarationHandle.Create(Prefix + "distanceTwo"),
                H("Exact distance two on the same vertices"),
                StatementSource.FromAuthor(DistanceFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every vertex type V and simple graph G on V, distanceTwo G is a simple graph on V with exactly this adjacency relation. SimpleGraph.edist is the extended natural shortest-walk distance; an unreachable pair has distance infinity, so is not adjacent here. Symmetry follows from SimpleGraph.edist_comm, and SimpleGraph.edist_self excludes loops."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("demo-period-positive-return"),
                DeclarationHandle.Create(Prefix + "PositiveReturn"),
                H("Positive isomorphism return"),
                StatementSource.FromAuthor(ReturnFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("PositiveReturn G t is a proposition. Function.iterate(distanceTwo,t,G) applies distanceTwo exactly t times, starting with G at t = 0. SimpleGraph.Iso is the graph-isomorphism type and Nonempty asserts that an isomorphism exists. In Definition 1 of the source the initial graph has index one, so its first return index is f = t + 1, with f > 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("demo-period-strong-period"),
                DeclarationHandle.Create(Prefix + "strongPeriod"),
                H("Least positive return, with zero for no return"),
                StatementSource.FromAuthor(PeriodFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("strongPeriod G is a natural number. These two exhaustive cases display its defining conditional: for an existence proof h, Nat.find h is the least t satisfying precisely PositiveReturn G t; if there is no such t, the value is zero. Thus zero is never a permitted return step. No finiteness or connectedness is required to define the operator, its return predicate, or this period."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("demo-period-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The complete universal bound of Conjecture 1"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("claim has type Prop and no parameters. The binder inst is the finite-type instance; Fintype.card(V,inst) displays that normally implicit instance explicitly. Both natural numbers are embedded into the integers by Int.ofNat before subtraction. There is no lower bound on the number of vertices, no nontriviality requirement and no positive-edge requirement."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("demo-period-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Refutation of the full universal claim"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Source, FixedPoints),
                Blocks(
                    Paragraph(Text("Take the edgeless simple graph on Unit. It is connected by SimpleGraph.Connected.of_subsingleton. Any two vertices coincide and their self-distance is zero, so distanceTwo G = G. Function.iterate_one and SimpleGraph.Iso.refl give PositiveReturn G 1. Nat.find_spec gives positivity of the least return and Nat.find_min' bounds it above by one; hence strongPeriod G = 1. Singleton cardinality then turns the asserted integer bound into 1 <= -2, a contradiction.")),
                    Paragraph(Text("The singleton fixed-point fact is already in the earlier metamour source: Theorem 4.1 characterizes edgeless fixed points, and the proof of Theorem 6.5 explicitly notes that the singleton has period one. The result here is the negation of the later paper's complete printed bound. It establishes no corrected bound for larger graphs and makes no claim of a new fixed-point theorem."))),
                DescribeRole.Theorem))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Named(owner), Dot, Named(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(name, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Graphs(Formula body) =>
        All("V", Seq(Named("Type"), Caret, Star),
            All("G", Call(Named("SimpleGraph"), F.Id("V")), body));
    private static Formula HasReturn() => new Formula.Bind(FormulaQuantifier.Exists,
        FormulaIdentifier.Create("t"), Seq(Mathbb, Grp(F.Id("N"))),
        Call(Named("PositiveReturn"), F.Id("G"), F.Id("t")));

    private static Formula DistanceFormula() => Disp(Graphs(
        All("u", F.Id("V"), All("v", F.Id("V"), IffFormula(
            Call(Qualified("SimpleGraph", "Adj"), Call(Named("distanceTwo"), F.Id("G")),
                F.Id("u"), F.Id("v")),
            Equal(Call(Qualified("SimpleGraph", "edist"), F.Id("G"), F.Id("u"), F.Id("v")), D(2)))))));

    private static Formula ReturnFormula() => Disp(Graphs(
        All("t", Seq(Mathbb, Grp(F.Id("N"))), IffFormula(
            Call(Named("PositiveReturn"), F.Id("G"), F.Id("t")),
            And(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("t")),
                Call(Named("Nonempty"), Call(Qualified("SimpleGraph", "Iso"),
                    Call(Qualified("Function", "iterate"), Named("distanceTwo"), F.Id("t"), F.Id("G")),
                    F.Id("G"))))))));

    private static Formula PeriodFormula() => Disp(Graphs(And(
        All("h", Parenthesized(HasReturn()),
            Equal(Call(Named("strongPeriod"), F.Id("G")), Call(Qualified("Nat", "find"), F.Id("h")))),
        ImpliesFormula(new Formula.Not(Parenthesized(HasReturn())),
            Equal(Call(Named("strongPeriod"), F.Id("G")), D(0))))));

    private static Formula ClaimFormula() => Disp(IffFormula(Named("claim"),
        All("V", Named("Type"),
            All("inst", Call(Named("Fintype"), F.Id("V")),
                All("G", Call(Named("SimpleGraph"), F.Id("V")),
                    ImpliesFormula(Call(Qualified("SimpleGraph", "Connected"), F.Id("G")),
                        new Formula.Relation(
                            Call(Qualified("Int", "ofNat"), Call(Named("strongPeriod"), F.Id("G"))),
                            FormulaRelationOperator.LessThanOrEqual,
                            new Formula.Binary(
                                Call(Qualified("Int", "ofNat"),
                                    Call(Qualified("Fintype", "card"), F.Id("V"), F.Id("inst"))),
                                FormulaBinaryOperator.Subtract, D(3)))))))));
}
