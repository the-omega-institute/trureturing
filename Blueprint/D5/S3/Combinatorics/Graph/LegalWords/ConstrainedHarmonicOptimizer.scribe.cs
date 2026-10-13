using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LegalWords;

internal sealed class ConstrainedHarmonicOptimizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constrained harmonic optimization on the complete Fibonacci cube",
        H("Constrained harmonic optimization"),
        Blocks(
            Describe.Lean(DescribeId.Create("harmonic"), DeclarationHandle.Create(Prefix + "harmonic"),
                H("The harmonic edge term"), StatementSource.FromAuthor(HarmonicFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real function h(s,t)=s*t/(s+t) uses total real division. In particular h(0,0)=0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("objective"), DeclarationHandle.Create(Prefix + "objective"),
                H("The complete original unordered-edge objective"), StatementSource.FromAuthor(ObjectiveFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Phi_n(p) sums h(p_b,p_c) over exactly the native unordered edgeFinset of legalWordGraph n on EdgeCount.Legal n. Every legal Hamming-one edge is included. This includes the zero word, both open-path endpoints and edges between consecutive blocks in any block notation. The existing deletion-edge bijection reindexes this same sum by the occupied upper word and its true position."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("epsilon-simplex"), DeclarationHandle.Create(Prefix + "epsilonSimplex"),
                H("The entire normalized positive simplex"), StatementSource.FromAuthor(SimplexFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("C_epsilon consists of every real vector with p_b>=epsilon at every original legal word and sum_b p_b=1. Insertion inequalities are not constraints defining this set. It is nonempty when epsilon<=1/M, where M is the number of original legal words, including equality and its uniform vector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("near"), DeclarationHandle.Create(Prefix + "Near"),
                H("Open-path position adjacency"), StatementSource.FromAuthor(NearFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positions i and j are neighbors when their natural indices differ by one. There is no cyclic identification."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("position-degree"), DeclarationHandle.Create(Prefix + "positionDegree"),
                H("The number of neighboring path positions"), StatementSource.FromAuthor(DegreeFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("d_i counts neighboring positions in Fin n. It is a position degree, distinct from the degree of a legal-word vertex."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("insertion-lower"), DeclarationHandle.Create(Prefix + "insertionLower"),
                H("The position-dependent ratio constant"), StatementSource.FromAuthor(RatioFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("q_i=(4-d_i)/(4+d_i). At length one this is 1, at an endpoint of a path of length at least two it is 3/5, and at an interior position it is 1/3."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("insertion-bounds"), DeclarationHandle.Create(Prefix + "InsertionBounds"),
                H("Bounds at every native upward insertion"), StatementSource.FromAuthor(BoundsFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original marked edge, upper y and lower x=erase y i satisfy q_i*p_x<=p_y<=p_x. The marked word is the upper endpoint, not the lower endpoint."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transfer"), DeclarationHandle.Create(Prefix + "transfer"),
                H("Conserved mass transfer on original coordinates"), StatementSource.FromAuthor(TransferFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transfer u adds u to the receiver and subtracts u from the donor. All other original coordinates are retained and the sum of coordinates is unchanged."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gradient"), DeclarationHandle.Create(Prefix + "gradient"),
                H("The native neighbor derivative sum"), StatementSource.FromAuthor(GradientFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a positive vector, g_b(p) is the sum over all native neighbors c of (p_c/(p_b+p_c))^2. The derivative of a donor-to-receiver transfer is g_receiver-g_donor."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("improving-transfer"), DeclarationHandle.Create(Prefix + "improving_transfer_of_bad_insertion"),
                H("A violated insertion forces a feasible improvement"), StatementSource.FromAuthor(ImprovementFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every n>=1, epsilon>0 and p in C_epsilon violating at least one insertion inequality, there exist an original adjacent donor and receiver with p_receiver<p_donor and a radius 0<delta<p_donor-epsilon. For every 0<u<delta the actual transfer belongs to C_epsilon and strictly increases Phi_n. The selected edge need not be the initially witnessed violation.")),
                    Paragraph(Text("If an upper bound fails, select the largest upward ratio over the entire original finite edge set. Inserting i pairs every upper neighbor other than x with a lower neighbor still admitting i. Each paired gradient term is no larger at the upper endpoint; all leftover lower terms are nonnegative. The edge term is strictly negative, so transferring from upper to lower improves the objective.")),
                    Paragraph(Text("After all upper bounds hold, select the smallest upward ratio in a violating direction i. The paired terms now favor the upper endpoint. Every leftover lower neighbor is a legal insertion at a neighboring position j, and its square share is at most 1/4. Their number is at most d_i. Thus g_upper-g_lower is at least (p_lower-p_upper)/(p_lower+p_upper)-d_i/4, strictly positive below q_i. Transfer from lower to upper. In both branches the donor has strict slack even if the receiver equals epsilon. The verified real derivative gives an actual positive feasible radius and strict objective increase.")),
                    Paragraph(Text("The complete-word and path-independent-set domain is the classical Fibonacci cube of Hsu and Codara--D'Antona. The formal theorem proves both extremal-ratio branches on the complete native edge set. Finite compactness and scalar calculus are standard tools."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("constrained-optimizer"), DeclarationHandle.Create(Prefix + "exists_constrained_optimizer_with_insertion_bounds"),
                H("The constrained maximum satisfies every insertion bound"), StatementSource.FromAuthor(MaximumFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every n>=1 and 0<epsilon<=1/M there exists p in the entire C_epsilon maximizing the actual unordered-edge harmonic objective and satisfying q_i*p_lower<=p_upper<=p_lower at every original insertion. Compactness and continuity give a maximum. A violating insertion would give the strict feasible improvement just established, contradicting that maximum.")),
                    Paragraph(Text("This is a constrained positive-simplex result. It does not establish full-simplex uniqueness, remove all active epsilon constraints, certify zero-coordinate competitors, construct a stationary probability law, or identify a geometric optimizer with any original integer maximizer. The full Robin obligation for all integers above 5040 and its fixed signed cofinal witness condition remain separate."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name)))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Not(Formula a) => Seq(Neg, Sp, Par(a));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Square(Formula a) => new Formula.Power(Par(a), D(2));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Legal(Formula n) => Call("Legal", n);
    private static Formula Vector(Formula n) => new Formula.TypeArrow(Legal(n), Real());
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Colon, Sp, type)), Sp, Par(body));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(name), Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula At(Formula p, Formula b) => new Formula.Apply(p, [b]);
    private static Formula Upper(Formula e) => Call("fst", e);
    private static Formula Position(Formula e) => Call("val", Call("snd", e));
    private static Formula Lower(Formula e) => Call("erase", Upper(e), Position(e));
    private static Formula Adj(Formula n, Formula a, Formula b) => Call("Adj", Call("legalWordGraph", n), a, b);
    private static Formula Simplex(Formula n, Formula eps) => Call("epsilonSimplex", n, eps);

    private static Formula HarmonicFormula()
    {
        Formula s = F.Id("s"), t = F.Id("t");
        return Disp(All("s", Real(), All("t", Real(), Equal(Call("harmonic", s, t), Div(Mul(s, t), Add(s, t))))));
    }

    private static Formula ObjectiveFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), a = F.Id("a"), b = F.Id("b"), e = F.Id("e");
        Formula edgeTerm = QCall("Sym2", "lift", Par(LambdaOf("a", Legal(n), Par(LambdaOf("b", Legal(n),
            Call("harmonic", At(p, a), At(p, b)))))), e);
        Formula sum = Seq(new Formula.Subscript(Sum, Mem(e, Call("edgeFinset", Call("legalWordGraph", n)))), Sp, edgeTerm);
        return Disp(All("n", Nat(), All("p", Vector(n), Equal(Call("objective", n, p), sum))));
    }

    private static Formula SimplexFormula()
    {
        Formula n = F.Id("n"), eps = F.Id("epsilon"), p = F.Id("p"), b = F.Id("b");
        return Disp(All("n", Nat(), All("epsilon", Real(), Equal(Simplex(n, eps), SetOf("p", Vector(n),
            And(All("b", Legal(n), Le(eps, At(p, b))), Equal(SumOver("b", Legal(n), At(p, b)), D(1))))))));
    }

    private static Formula NearFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        return Disp(All("n", Nat(), All("i", Call("Fin", n), All("j", Call("Fin", n),
            Iff(Call("Near", i, j), Or(Equal(Add(Call("val", i), D(1)), Call("val", j)),
                Equal(Add(Call("val", j), D(1)), Call("val", i))))))));
    }

    private static Formula DegreeFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        return Disp(All("n", Nat(), All("i", Call("Fin", n), Equal(Call("positionDegree", i),
            Call("card", SetOf("j", Call("Fin", n), Call("Near", i, j)))))));
    }

    private static Formula RatioFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), d = Call("positionDegree", i);
        return Disp(All("n", Nat(), All("i", Call("Fin", n),
            Equal(Call("insertionLower", i), Div(Sub(D(4), d), Add(D(4), d))))));
    }

    private static Formula BoundsFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), e = F.Id("e");
        return Disp(All("n", Nat(), All("p", Vector(n), Iff(Call("InsertionBounds", n, p),
            All("e", Call("Marked", n), And(
                Le(Mul(Call("insertionLower", Position(e)), At(p, Lower(e))), At(p, Upper(e))),
                Le(At(p, Upper(e)), At(p, Lower(e)))))))));
    }

    private static Formula TransferFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), d = F.Id("donor"), r = F.Id("receiver"), u = F.Id("u"), b = F.Id("b");
        Formula indicator(Formula c) => Seq(Operatorname, Grp(F.Id("if")), Sp, Equal(b, c), Sp,
            Operatorname, Grp(F.Id("then")), Sp, D(1), Sp, Operatorname, Grp(F.Id("else")), Sp, D(0));
        return Disp(All("n", Nat(), All("p", Vector(n), All("donor", Legal(n), All("receiver", Legal(n),
            All("u", Real(), All("b", Legal(n), Equal(At(Call("transfer", p, d, r, u), b),
                Add(At(p, b), Mul(u, Sub(Par(indicator(r)), Par(indicator(d)))))))))))));
    }

    private static Formula GradientFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), b = F.Id("b"), z = F.Id("z"), vz = Call("val", z);
        Formula neighbors = SetOf("z", Legal(n), Adj(n, b, z));
        return Disp(All("n", Nat(), All("p", Vector(n), All("b", Legal(n),
            Equal(Call("gradient", p, b), SumOver("z", neighbors,
                Square(Div(At(p, vz), Add(At(p, b), At(p, vz))))))))));
    }

    private static Formula ImprovementFormula()
    {
        Formula n = F.Id("n"), eps = F.Id("epsilon"), p = F.Id("p"), d = F.Id("donor"), r = F.Id("receiver"),
            delta = F.Id("delta"), u = F.Id("u");
        Formula step = Call("transfer", p, d, r, u);
        Formula gain = All("u", Real(), Imp(And(Less(D(0), u), Less(u, delta)), And(
            Mem(step, Simplex(n, eps)), Less(Call("objective", n, p), Call("objective", n, step)))));
        Formula result = Ex("donor", Legal(n), Ex("receiver", Legal(n), And(Adj(n, d, r),
            And(Less(At(p, r), At(p, d)), Ex("delta", Real(), And(Less(D(0), delta),
                And(Less(delta, Sub(At(p, d), eps)), gain)))))));
        return Disp(All("n", Nat(), All("epsilon", Real(), All("p", Vector(n),
            Imp(And(Le(D(1), n), And(Less(D(0), eps), And(Mem(p, Simplex(n, eps)),
                Not(Call("InsertionBounds", n, p))))), result)))));
    }

    private static Formula MaximumFormula()
    {
        Formula n = F.Id("n"), eps = F.Id("epsilon"), p = F.Id("p");
        Formula result = Ex("p", Vector(n), And(Mem(p, Simplex(n, eps)),
            And(Call("IsMaxOn", Call("objective", n), Simplex(n, eps), p), Call("InsertionBounds", n, p))));
        return Disp(All("n", Nat(), All("epsilon", Real(), Imp(
            And(Le(D(1), n), And(Less(D(0), eps), Le(eps, Div(D(1), Call("card", Legal(n)))))), result))));
    }
}
