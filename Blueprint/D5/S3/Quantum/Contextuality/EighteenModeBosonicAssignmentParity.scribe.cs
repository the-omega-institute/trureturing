using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class EighteenModeBosonicAssignmentParityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Observer/kurzynski2017contextualityidentical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eighteen-mode bosonic occupation model admits an assignment exactly for even particle numbers.",
        H("Parity of eighteen-mode bosonic occupation assignments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("modes"),
                DeclarationHandle.Create(Module + ".modes"),
                H("The eighteen modes"),
                StatementSource.FromAuthor(Disp(ModesFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Each pair (i,j) labels the mode shared by contexts i and j. "
                    + "The eighteen pairs give the mode labels in Kurzyński's eighteen-projector set. "
                    + "The interpretation of the labels is stated in contextuality_fermions.tex, line 83; "
                    + "the nine contexts are displayed in lines 132–221. "
                    + "Context i consists of precisely "
                    + "the pairs in modes whose first or second coordinate equals i."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncontextual-assignment"),
                DeclarationHandle.Create(Module + ".IsNoncontextualAssignment"),
                H("Context-independent occupations with conserved particle number"),
                StatementSource.FromAuthor(Disp(AssignmentFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a natural particle number n, one function v assigns a natural occupation "
                    + "to each pair of natural numbers. The same value is used whenever a mode "
                    + "occurs in either of its contexts. Each of the nine context sums must equal n, "
                    + "as required by equation (1) and the bosonic occupation model in "
                    + "contextuality_fermions.tex, lines 74–81. Values on pairs outside modes "
                    + "do not enter any of these sums."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The particle numbers admitting an occupation assignment"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimFormula()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n, a context-independent occupation assignment exists "
                    + "if and only if n is even. This includes n equal to zero. "
                    + "It gives a classification in the occupation-assignment model addressing "
                    + "the question for more than two bosons in contextuality_fermions.tex, line 233."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Existence is equivalent to even particle number"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First count the contexts containing a fixed mode p. Its two coordinates "
                        + "are distinct and both lie between 1 and 9, as follows by checking the "
                        + "eighteen listed pairs. Membership in context i is equivalent to p.1 = i "
                        + "or p.2 = i. Since the coordinates are distinct, the indicator of this "
                        + "disjunction is the sum of the two coordinate indicators. Summing over "
                        + "i from 1 to 9 therefore gives two occurrences of p.")),
                    Paragraph(Text(
                        "Express each context sum as a sum over all eighteen modes, with zero "
                        + "contribution from modes outside that context. Interchange the finite "
                        + "sums, factor each occupation v(p) out of its sum of incidence indicators, "
                        + "and use the count of two. Factoring out this common multiplier gives:")),
                    new DocumentBlock.DisplayFormula(TotalFormula()),
                    Paragraph(Text(
                        "If v is an assignment for n, its nine context sums also total 9n. "
                        + "Consequently 9n equals twice the sum of the eighteen occupations, "
                        + "so 9n is even. Evenness of a product of natural numbers implies "
                        + "evenness of at least one factor; since 9 is odd, n is even.")),
                    Paragraph(Text(
                        "Conversely, for a natural m define v(p) to be m on "
                        + "{(1,2),(1,6),(2,8),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9)} "
                        + "and zero elsewhere. Check the nine contexts individually: their selected "
                        + "pairs are respectively {(1,2),(1,6)}, {(1,2),(2,8)}, "
                        + "{(3,7),(3,9)}, {(4,7),(4,8)}, {(5,6),(5,9)}, "
                        + "{(1,6),(5,6)}, {(3,7),(4,7)}, {(2,8),(4,8)} and {(3,9),(5,9)}. "
                        + "Thus each sum of support indicators is two. Each occupation sum "
                        + "is that indicator sum multiplied by m, and hence equals 2m:")),
                    new DocumentBlock.DisplayFormula(EvenConstructionFormula()),
                    Paragraph(Text(
                        "For any n, an assignment therefore implies that n is even. "
                        + "In the reverse direction, express an even n as 2m and apply the "
                        + "construction just given. This proves both directions for every natural n. "
                        + "In particular every odd particle number, including three, is excluded, "
                        + "whereas zero and every even particle number admit an assignment. "
                        + "The classification concerns the existence of occupation assignments "
                        + "for these nine contexts."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kurzynski-2017-eighteen-mode-bosonic-assignment-parity"),
                    ResolutionKind.Proved)))));

    private static Formula ModesFormula() => Equal(
        Typed(Local("modes"), At(Qualified("Finset"), PairType())),
        new Formula.SetLiteral([
            Pair(1, 2), Pair(1, 6), Pair(1, 7), Pair(1, 8), Pair(2, 3), Pair(2, 8),
            Pair(2, 9), Pair(3, 4), Pair(3, 7), Pair(3, 9), Pair(4, 5), Pair(4, 7),
            Pair(4, 8), Pair(5, 6), Pair(5, 8), Pair(5, 9), Pair(6, 7), Pair(6, 9)]));

    private static Formula AssignmentFormula() => All("n", Naturals(), All("v", Occupations(),
        Equivalence(LocalCall("IsNoncontextualAssignment", X("n"), X("v")),
            All("i", Naturals(), ImpliesFormula(Member(X("i"), Contexts()),
                Equal(ContextSum(X("i"), X("v")), X("n")))))));

    private static Formula ClaimFormula() => All("n", Naturals(), Equivalence(
        Some("v", Occupations(), LocalCall("IsNoncontextualAssignment", X("n"), X("v"))),
        At(Qualified("Even"), X("n"))));

    private static Formula TotalFormula() => All("v", Occupations(), Equal(
        SumOver("i", Naturals(), Contexts(), ContextSum(X("i"), X("v"))),
        Multiply(D(2), SumOver("p", PairType(), Local("modes"), At(X("v"), X("p"))))));

    private static Formula EvenConstructionFormula() => All("m", Naturals(),
        LocalCall("IsNoncontextualAssignment", Multiply(D(2), X("m")),
            LambdaOf("p", PairType(), At(Qualified("ite"), Member(X("p"),
                new Formula.SetLiteral([
                    Pair(1, 2), Pair(1, 6), Pair(2, 8), Pair(3, 7), Pair(3, 9),
                    Pair(4, 7), Pair(4, 8), Pair(5, 6), Pair(5, 9)])), X("m"), D(0)))));

    private static Formula ContextSum(Formula i, Formula v) => SumOver("p", PairType(),
        At(Qualified("D5", "S3", "Combinatorics", "Graph", "BipartiteSubgraphDensity", "incident"),
            Local("modes"), Qualified("Prod", "fst"), Qualified("Prod", "snd"), i),
        At(v, X("p")));

    private static Formula Contexts() => At(Qualified("Finset", "Icc"), D(1), D(9));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula PairType() => Seq(Naturals(), Sp, Times, Sp, Naturals());
    private static Formula Occupations() => new Formula.TypeArrow(Parenthesized(PairType()), Naturals());
    private static Formula Pair(byte a, byte b) => Parenthesized(Seq(D(a), Comma, Sp, D(b)));
    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Contextuality",
        "EighteenModeBosonicAssignmentParity", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(Typed(X(name), type), set)), Sp, Parenthesized(body));
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
}
