using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class GlauberNeighbourhoodPassivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/luozhenliueblerdahlsten2023annealing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Petersen-graph Glauber annealing run violates neighbourhood passivity.",
        H("Neighbourhood passivity is not preserved by Glauber annealing"), Blocks(
            Paragraph(Text(
                "The finite state space is Fin N. Energies, inverse temperatures and populations are real-valued, "
                    + "and populations are columns. The relation A describes a regular neighbourhood, while beta "
                    + "is the inverse-temperature schedule. All sums over Fin N include every state; a sum indexed "
                    + "by membership in a filtered Finset ranges over exactly the displayed neighbours. "
                    + "The bracketed DecidableRel A is an anonymous instance argument.")),
            Node("neighbourhoodPassivity", "Neighbourhood passivity at the next temperature",
                NeighbourhoodPassivityFormula(),
                "For state i at step k, the Gibbs weights are evaluated at beta(k + 1), while the population "
                    + "differences use p(k). The sum runs over the states adjacent to i and is the ratio-weighted "
                    + "passivity expression in Eq. (41). The five reused annealing definitions are displayed below.",
                AssessedProvenance.FromLiterature(Source),
                new DocumentBlock.DisplayFormula(RegularNeighborhoodFormula()),
                new DocumentBlock.DisplayFormula(GibbsFormula()),
                new DocumentBlock.DisplayFormula(EdgeWeightFormula()),
                new DocumentBlock.DisplayFormula(GlauberFormula()),
                new DocumentBlock.DisplayFormula(SARunFormula())),
            Node("claim", "The neighbourhood-passivity expectation", ClaimFormula(),
                "The source expects every connected regular neighbourhood with distinct energies to preserve "
                    + "nonnegative neighbourhood passivity throughout a Glauber annealing run started in the Gibbs "
                    + "state. The schedule is strictly increasing and starts at a positive inverse temperature. "
                    + "The conclusion quantifies over every step and every state.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("glauber-neighbourhood-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A Petersen graph gives negative neighbourhood passivity"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use the Petersen graph on ten states. Its neighbour sets, in order from 0 through 9, are "
                            + "{1,4,5}, {0,2,6}, {1,3,7}, {2,4,8}, {0,3,9}, {0,7,8}, {1,8,9}, "
                            + "{2,5,9}, {3,5,6}, and {4,6,7}. Every state has three neighbours, the relation "
                            + "is symmetric and irreflexive, and the graph is connected.")),
                    Paragraph(Text(
                        "The energy vector on states 0 through 9 is (3,4,6,7,5,2,8,0,1,9). "
                            + "The inverse-temperature schedule is beta(0) = log(11/10) and "
                            + "beta(k) = log(4k) for every k at least 1; the first three values used here are "
                            + "log(11/10), log 4, and log 8. Start with the Gibbs population at log(11/10) "
                            + "and apply the Glauber matrix at the next scheduled temperature.")),
                    Paragraph(Text(
                        "The exact first population is "
                            + "(6495040420/47812273803, 1579228369400/12287754367371, "
                            + "531822026923/11522757986523, 160582769930/11522757986523, "
                            + "442180927000/4095918122457, 4048016885/47812273803, "
                            + "49100916611546/1388516243512923, 2707415959783376/11662677190645065, "
                            + "268789869032696/1302071652477099, 782236372623151/87058739692823535). "
                            + "It is obtained by one exact matrix-vector multiplication.")),
                    Paragraph(Text(
                        "At step 1 and state 0, the three neighbours have energies 4, 5 and 2. "
                            + "At beta(2) = log 8, the corresponding Gibbs-ratio weights are 7/9, 63/65 and "
                            + "−7/9. Substitution of the exact first population gives "
                            + "P_0(1) = −1454086156987/205381037283201, which is negative. "
                            + "Thus the universal nonnegativity assertion fails."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("luo-zhen-liu-ebler-dahlsten-2023-neighbourhood-passivity-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance,
        params DocumentBlock[] additionalBlocks)
    {
        var blocks = new List<DocumentBlock> { Paragraph(Text(prose)) };
        blocks.AddRange(additionalBlocks);
        return Describe.Lean(
            DescribeId.Create("glauber-neighbourhood-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(blocks.ToArray()), DescribeRole.Definition);
    }

    private static Formula NeighbourhoodPassivityFormula()
    {
        Formula next = Add(V("k"), D(1));
        Formula gammaI = OwnerCall("gibbs", V("E"), At(V("beta"), next), V("i"));
        Formula gammaJ = OwnerCall("gibbs", V("E"), At(V("beta"), next), V("j"));
        Formula ratio = new Formula.Fraction(Subtract(gammaI, gammaJ), Add(gammaI, gammaJ));
        Formula populationDifference = Subtract(At(V("p"), V("k"), V("i")), At(V("p"), V("k"), V("j")));
        Formula neighbours = At(Qualified("Finset", "filter"),
            LambdaOf("j", FinType(), At(V("A"), V("i"), V("j"))),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), FinType())));
        Formula sum = SumIn("j", neighbours, Multiply(ratio, populationDifference));
        return GraphBinders(EnergyBinder(RunBinders(All("k", Naturals(), All("i", FinType(),
            Equal(LocalCall("neighbourhoodPassivity", V("n"), V("A"), V("E"), V("beta"), V("p"),
                V("k"), V("i")), sum))))));
    }

    private static Formula ClaimFormula()
    {
        Formula connected = At(Qualified("SimpleGraph", "Connected"),
            At(Qualified("SimpleGraph", "fromRel"), V("A")));
        Formula body = All("k", Naturals(), All("i", FinType(),
            LE(D(0), LocalCall("neighbourhoodPassivity", V("n"), V("A"), V("E"), V("beta"), V("p"),
                V("k"), V("i")))));
        Formula[] hypotheses =
        [
            OwnerCall("regularNeighborhood", V("n"), V("A")),
            connected,
            At(Qualified("Function", "Injective"), V("E")),
            At(Qualified("StrictMono"), V("beta")),
            LT(D(0), At(V("beta"), D(0))),
            OwnerCall("isSARun", V("n"), V("A"), V("E"), V("beta"), V("p"))
        ];
        for (var index = hypotheses.Length - 1; index >= 0; index--)
            body = Imp(hypotheses[index], body);
        return IffOf(Local("claim"), GraphBinders(EnergyBinder(RunBinders(body))));
    }

    private static Formula RegularNeighborhoodFormula()
    {
        Formula neighbours = At(Qualified("Finset", "filter"),
            LambdaOf("i", FinType(), At(V("A"), V("i"), V("j"))),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), FinType())));
        Formula conditions = And(LE(D(1), V("n")),
            And(All("i", FinType(), All("j", FinType(),
                    Imp(At(V("A"), V("i"), V("j")), At(V("A"), V("j"), V("i"))))),
                And(All("i", FinType(), new Formula.Not(Parenthesized(At(V("A"), V("i"), V("i"))))),
                    All("j", FinType(), Equal(At(Qualified("Finset", "card"), neighbours), V("n"))))));
        return GraphBinders(IffOf(OwnerCall("regularNeighborhood", V("n"), V("A")), conditions));
    }

    private static Formula GibbsFormula()
    {
        Formula weight = At(Qualified("Real", "exp"), Multiply(new Formula.Negate(V("b")), At(V("E"), V("i"))));
        Formula normalization = SumOver("j",
            At(Qualified("Real", "exp"), Multiply(new Formula.Negate(V("b")), At(V("E"), V("j")))));
        return SizeBinder(EnergyBinder(All("b", Reals(), All("i", FinType(),
            Equal(OwnerCall("gibbs", V("E"), V("b"), V("i")), new Formula.Fraction(weight, normalization))))));
    }

    private static Formula EdgeWeightFormula()
    {
        Formula numerator = OwnerCall("gibbs", V("E"), V("b"), V("i"));
        Formula denominator = Multiply(Typed(V("n"), Reals()),
            Add(OwnerCall("gibbs", V("E"), V("b"), V("i")), OwnerCall("gibbs", V("E"), V("b"), V("j"))));
        return GraphBinders(EnergyBinder(All("b", Reals(), IndexBinders(
            Equal(OwnerCall("edgeWeight", V("n"), V("A"), V("E"), V("b"), V("i"), V("j")),
                Conditional(At(V("A"), V("i"), V("j")), new Formula.Fraction(numerator, denominator), D(0)))))));
    }

    private static Formula GlauberFormula()
    {
        Formula diagonal = Subtract(D(1), SumOver("l",
            OwnerCall("edgeWeight", V("n"), V("A"), V("E"), V("b"), V("l"), V("j"))));
        Formula offDiagonal = OwnerCall("edgeWeight", V("n"), V("A"), V("E"), V("b"), V("i"), V("j"));
        return GraphBinders(EnergyBinder(All("b", Reals(), IndexBinders(
            Equal(OwnerCall("glauber", V("n"), V("A"), V("E"), V("b"), V("i"), V("j")),
                Conditional(Equal(V("i"), V("j")), diagonal, offDiagonal))))));
    }

    private static Formula SARunFormula()
    {
        Formula next = Add(V("t"), D(1));
        Formula transition = OwnerCall("glauber", V("n"), V("A"), V("E"), At(V("beta"), next));
        Formula recursion = All("t", Naturals(), Equal(At(V("p"), next),
            At(Qualified("Matrix", "mulVec"), transition, At(V("p"), V("t")))));
        Formula conditions = And(All("t", Naturals(),
            At(Qualified("D5", "S3", "TotalVariation", "CycleSingleCutMinimax", "Probability"), At(V("p"), V("t")))),
            And(Equal(At(V("p"), D(0)), OwnerCall("gibbs", V("E"), At(V("beta"), D(0)))), recursion));
        return And(ProbabilityFormula(), GraphBinders(EnergyBinder(RunBinders(
            IffOf(OwnerCall("isSARun", V("n"), V("A"), V("E"), V("beta"), V("p")), conditions)))));
    }

    private static Formula ProbabilityFormula() => SizeBinder(All("p", States(),
        IffOf(At(Qualified("D5", "S3", "TotalVariation", "CycleSingleCutMinimax", "Probability"), V("p")),
            And(All("i", FinType(), LE(D(0), At(V("p"), V("i")))),
                Equal(SumOver("i", At(V("p"), V("i"))), D(1))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula OwnerCall(string name, params Formula[] args) =>
        At(Owner(name), args);
    private static Formula Local(string name) => Qualified("D5", "S3", "StatisticalMechanics",
        "GlauberNeighbourhoodPassivityRefutation", name);
    private static Formula Owner(string name) => Qualified("D5", "S3", "StatisticalMechanics",
        "GlauberRelaxationOrderRefutation", name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula FinType() => At(Qualified("Fin"), V("N"));
    private static Formula States() => Parenthesized(new Formula.TypeArrow(FinType(), Reals()));
    private static Formula SizeBinder(Formula body) => All("N", Naturals(), body);
    private static Formula GraphBinders(Formula body) => SizeBinder(All("n", Naturals(),
        All("A", Parenthesized(new Formula.TypeArrow(FinType(),
            new Formula.TypeArrow(FinType(), Qualified("Prop")))),
            Seq(Seq(OpenBracket, At(Qualified("DecidableRel"), V("A")), CloseBracket), Sp,
                Parenthesized(body)))));
    private static Formula EnergyBinder(Formula body) => All("E", States(), body);
    private static Formula RunBinders(Formula body) =>
        All("beta", Parenthesized(new Formula.TypeArrow(Naturals(), Reals())),
            All("p", Parenthesized(new Formula.TypeArrow(Naturals(), States())), body));
    private static Formula IndexBinders(Formula body) => All("i", FinType(), All("j", FinType(), body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), FinType())), Sp, Parenthesized(body));
    private static Formula SumIn(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, new Formula.Relation(V(name), FormulaRelationOperator.MemberOf, set)),
            Sp, Parenthesized(body));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Word("if"), Sp, Parenthesized(condition), Sp, Word("then"), Sp,
            Parenthesized(yes), Sp, Word("else"), Sp, Parenthesized(no));
    private static Formula Word(string word) => Seq(Mathrm, Grp(V(word)));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
