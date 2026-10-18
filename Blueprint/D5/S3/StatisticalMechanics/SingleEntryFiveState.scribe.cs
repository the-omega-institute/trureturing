using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SingleEntryFiveStateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/SingleEntryFiveState.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict transient association from the five-state single-entry forward equations.",
        H("A repressed initial state creates strict two-site association"),
        Blocks(
            Node("Rates", "Positive rates",
                "The rate tuple k contains six arbitrary strictly positive real rates. The first site's binding and unbinding rates are a,b; the second site's are c,d. Entry from 00 to R has rate eta, and return from R to 00 has rate theta.", DescribeRole.Definition),
            Node("generator", "The actual five-state generator",
                "States are R,00,10,01,11, in that order. Within the Boolean square, only one bit flips at a time, with its site's stated binding or unbinding rate. The only extra edge is 00 to R at eta and R to 00 at theta. Columns sum to zero and diagonal entries are minus total outgoing rates.", DescribeRole.Definition),
            Node("ForwardSolution", "The independent dynamical contract",
                "A trajectory p starts at unit mass in R and solves p'=Q p at every nonnegative real time, with Q equal to the stated generator. This contract contains no association or monotonicity hypothesis.", DescribeRole.Definition),
            Node("activeMass", "Active mass",
                "r(p,t)=1-p(t,R).", DescribeRole.Definition),
            Node("firstOccupancy", "First occupancy",
                "X(p,t)=p(t,10)+p(t,11). The inhibited state R does not belong to this event.", DescribeRole.Definition),
            Node("secondOccupancy", "Second occupancy",
                "Y(p,t)=p(t,01)+p(t,11). The inhibited state R does not belong to this event.", DescribeRole.Definition),
            Node("association", "Conditional association residual",
                "D(p,t)=r(p,t) p(t,11)-X(p,t)Y(p,t). Conservation of total mass identifies this with p(t,00)p(t,11)-p(t,10)p(t,01).", DescribeRole.Definition),
            Node("fiberWidth", "Probability fiber width",
                "w(p,t)=min{X(p,t),Y(p,t),r(p,t)-X(p,t),r(p,t)-Y(p,t)}. The three occupancy means are coordinates of one five-mode source.", DescribeRole.Definition),
            Node("canonicalTrajectory", "The generated probability law",
                "The trajectory p(t,i) is the (i,R) entry of exp(t Q), where Q is the independently specified generator. It starts at unit mass in R, solves the forward equations, is nonnegative for nonnegative time and has total mass one.", DescribeRole.Definition),
            Node("pyramidLaw", "The actual five-mode law",
                "Reorder the same trajectory as 000,100,010,001,101: the masses are p(00),p(10),p(R),p(01),p(11). Thus the established chart's three visible occupancies are exactly X,Y,p(R), with no new label or extra site.", DescribeRole.Definition),
            Node("independentCompletion", "Conditional independent completion",
                "Keep the inhibited mass p(R). On the active square use masses (r-X)(r-Y)/r, X(r-Y)/r, (r-X)Y/r, XY/r in order 00,10,01,11. This formula is used only when r>0.", DescribeRole.Definition),
            Node("taskContrast", "Task interaction",
                "For a task f on the actual five states, J=f(11)-f(10)-f(01)+f(00).", DescribeRole.Definition),
            Node("taskError", "Actual expectation error",
                "Subtract the task expectation under the conditionally independent completion from the expectation under the actual law at the same time.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("single-entry-five-state-strict-association"),
                DeclarationHandle.Create(Prefix + "five_state_strict_association"),
                H("Strict association at every positive time"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A probability-valued forward solution exists and has all five masses strictly positive at every positive time. Its actual occupancy law lies in the established open five-mode simplex and projects to the open pyramid. Every forward solution starting at R has r>0, w>0 and D>0 at every positive time. Since 10 and 01 are the only incomparable configurations of the two-dimensional Boolean square, its conditional law is strictly MTP2. In addition theta p(R)-eta p(00)>0, so the active mass increases strictly. No positive-association premise is imposed. The generator is similar to minus a symmetric Gram matrix built from its five actual edges. Projection of the same trajectory onto an orthogonal eigenbasis gives a positive spectral representation of its return probability. The positive R diagonal ensures that at least one positive eigenvalue carries nonzero return weight, hence strictly positive net return at every finite time. Scalar integrating factors propagate that strict input through r, both occupied and vacant margins, the double occupancy, and finally D' = -(a+b+c+d)D + r' p(11). Existence uses exp(t Q); entrywise nonnegativity follows by a scalar diagonal shift to an entrywise nonnegative matrix and its exponential series, and conservation follows from the column sums. For every real task on these same five physical states, actual minus independently completed expectation is exactly J D/r. Multiplication by a nonzero J gives a strictly positive result, proving nonzero error with the sign of J. The task identity uses the actual conserved mass and four-corner table; it does not posit a residual as a premise. The theorem does not assert the general-dimensional result, equilibrium limit or common-tail coefficient. The chart is reused directly from FiveModeMixedCoordinates.mixed_coordinates_global_chart. No original Fibonacci reader, guard or continuation law is inferred from this occupancy correspondence."))), DescribeRole.Theorem))));

    private static DocumentBlock Node(string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("single-entry-five-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula All(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Exists(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Pos(Formula x) => Rel(D(0), FormulaRelationOperator.LessThan, x);
    private static Formula TheoremFormula()
    {
        Formula k = F.Id("k"), p = F.Id("p"), t = F.Id("t");
        Formula f = F.Id("f");
        Formula contrast = Call("taskContrast", f), error = Call("taskError", p, f, t);
        Formula task = All("f", Seq(Call("Fin", D(5)), Sp, To, Sp, R()), And(
            Rel(error, FormulaRelationOperator.Equal,
                new Formula.Fraction(Mul(contrast, Call("association", p, t)),
                    Call("activeMass", p, t))),
            Imp(Rel(contrast, FormulaRelationOperator.NotEqual, D(0)), Pos(Mul(contrast, error)))));
        Formula result = And(Pos(Call("activeMass", p, t)),
            And(Pos(Call("fiberWidth", p, t)), And(Pos(Call("association", p, t)),
                And(Rel(Mul(Call("p", t, D(2)), Call("p", t, D(3))),
                    FormulaRelationOperator.LessThan, Mul(Call("p", t, D(1)), Call("p", t, D(4)))),
                    And(Pos(Sub(Mul(Call("theta", k), Call("p", t, D(0))),
                        Mul(Call("eta", k), Call("p", t, D(1))))), task)))));
        Formula curve = Seq(R(), Sp, To, Sp, Call("Fin", D(5)), Sp, To, Sp, R());
        Formula nonnegative = All("t", R(), Imp(
            Rel(D(0), FormulaRelationOperator.LessThanOrEqual, t),
            And(All("i", Call("Fin", D(5)), Rel(D(0), FormulaRelationOperator.LessThanOrEqual,
                Call("p", t, F.Id("i")))),
                Rel(Seq(new Formula.Subscript(Sum, Seq(F.Id("i"), Colon, Call("Fin", D(5)))),
                    Sp, Call("p", t, F.Id("i"))),
                    FormulaRelationOperator.Equal, D(1)))));
        Formula law = Call("pyramidLaw", p, t);
        Formula interior = All("t", R(), Imp(Pos(t), And(
            Rel(law, FormulaRelationOperator.MemberOf, F.Id("openSimplex")),
            Rel(Call("visible", law), FormulaRelationOperator.MemberOf, F.Id("openPyramid")))));
        Formula existence = Exists("p", curve,
            And(Call("ForwardSolution", k, p), And(nonnegative, interior)));
        return Disp(All("k", F.Id("Rates"), And(existence, All("p", curve,
            Imp(Call("ForwardSolution", k, p), All("t", R(), Imp(Pos(t), result)))))));
    }
}
