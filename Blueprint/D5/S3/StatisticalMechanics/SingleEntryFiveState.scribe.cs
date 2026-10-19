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
            Describe.Lean(DescribeId.Create("single-entry-constant-nonnegative-time"),
                DeclarationHandle.Create(Prefix + "constant_on_nonneg"),
                H("A zero derivative fixes the trajectory"),
                StatementSource.FromAuthor(ConstantFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If a real function has derivative zero at every nonnegative time, its value at every nonnegative time equals its initial value. This helper is consumed by the scalar decay equations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("single-entry-positive-forcing"),
                DeclarationHandle.Create(Prefix + "positive_forcing"),
                H("Positive input gives a positive response"),
                StatementSource.FromAuthor(ForcingFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary real decay coefficient, a zero-initial scalar response satisfying f'=-cf+g is strictly positive at every positive time when g is strictly positive there. Multiplying by exp(ct) gives a strictly increasing response. The helper is consumed by the actual occupied and vacant margins and association residual."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("single-entry-symmetric-return-data"),
                DeclarationHandle.Create(Prefix + "symmetric_return_data"),
                H("The same symmetric evolution supplies return weights and its limit"),
                StatementSource.FromAuthor(SymmetricFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let A be a finite real positive semidefinite matrix with positive diagonal at o. The curve starts at the unit vector o and solves y'=-Ay. The returned rates are the Hermitian eigenvalues of A, and its nonnegative return weights are the squared entries U(o,j) of the orthogonal eigenvector matrix U. They sum to one and some positive rate has positive weight. The return probability is their exponential sum and has strictly negative derivative at every nonnegative time. Every coordinate converges to a vector L in the kernel of A. The full coordinate expansion is y(t,i)=sum_j U(i,j)U(o,j)exp(-ell(j)t). In the formula curveAt(y,t) means the vector i mapped to y(t,i), coordinateCurve(y,i) means t mapped to y(t,i), and U is eigenvectorUnitary(A)."))), DescribeRole.Theorem),
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
            Node("equilibriumLaw", "The stationary five-mode law",
                "Let C=theta(a+b)(c+d)+eta b d. In state order R,00,10,01,11 the candidate masses are eta b d/C, theta b d/C, theta a d/C, theta b c/C, theta a c/C. They are strictly positive, sum to one and solve Q pi=0. For this stationary law D=0 and w>0, and r=theta/(theta+eta(b/(a+b))(d/(c+d))). In the formula constant(v) denotes the time-constant curve with value v. The theorem also proves that every forward solution from R converges coordinatewise to this law. In the formula coordinateCurve(p,i) denotes u mapped to p(u,i), associationCurve(p) denotes u mapped to D(p,u), and activeMassCurve(p) denotes u mapped to r(p,u).", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("single-entry-five-state-strict-association"),
                DeclarationHandle.Create(Prefix + "five_state_strict_association"),
                H("Strict association at every positive time"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A probability-valued forward solution exists and has all five masses strictly positive at every positive time. Its actual occupancy law lies in the established open five-mode simplex and projects to the open pyramid. Every forward solution starting at R has r>0, w>0 and D>0 at every positive time. Since 10 and 01 are the only incomparable configurations of the two-dimensional Boolean square, its conditional law is strictly MTP2. In addition theta p(R)-eta p(00)>0, so the active mass increases strictly. No positive-association premise is imposed. The generator is similar to minus a symmetric Gram matrix built from its five actual edges. Projection of the same trajectory onto an orthogonal eigenbasis gives a positive spectral representation of its return probability. The positive R diagonal ensures that at least one positive eigenvalue carries nonzero return weight, hence strictly positive net return at every finite time. The public conclusion also supplies nonnegative mode rates and nonnegative return weights summing to one, with at least one strictly positive rate-weight product, whose exponential sum equals p(R) for all nonnegative times. The rates in this representation are not identified with the secular root. Scalar integrating factors propagate that strict input through r, both occupied and vacant margins, the double occupancy, and finally D' = -(a+b+c+d)D + r' p(11). Existence uses exp(t Q); entrywise nonnegativity follows by a scalar diagonal shift to an entrywise nonnegative matrix and its exponential series, and conservation follows from the column sums. For every real task on these same five physical states, actual minus independently completed expectation is exactly J D/r. Multiplication by a nonzero J gives a strictly positive result, proving nonzero error with the sign of J. The task identity uses the actual conserved mass and four-corner table; it does not posit a residual as a premise. The finite eigenmode expansion converges to its zero-mode projection. This projection is stationary for the original generator and has total mass one; solving the independent five-state equations identifies it with the stated equilibrium law. Consequently D tends to zero and r tends to theta/(theta+eta(b/(a+b))(d/(c+d))). The theorem does not assert the general-dimensional result or common-tail coefficient. The chart is reused directly from FiveModeMixedCoordinates.mixed_coordinates_global_chart. No original Fibonacci reader, guard or continuation law is inferred from this occupancy correspondence."))), DescribeRole.Theorem))));

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
    private static Formula ConstantFormula()
    {
        Formula f = F.Id("f"), u = F.Id("u"), t = F.Id("t");
        Formula nonneg = Rel(D(0), FormulaRelationOperator.LessThanOrEqual, u);
        return Disp(All("f", Seq(R(), Sp, To, Sp, R()),
            Imp(All("u", R(), Imp(nonneg, Call("HasDerivAt", f, D(0), u))),
            All("t", R(), Imp(Rel(D(0), FormulaRelationOperator.LessThanOrEqual, t),
                Rel(Call("f", t), FormulaRelationOperator.Equal, Call("f", D(0))))))));
    }
    private static Formula ForcingFormula()
    {
        Formula f = F.Id("f"), g = F.Id("g"), c = F.Id("c"), u = F.Id("u"), t = F.Id("t");
        Formula rhs = new Formula.Binary(Seq(Minus, c, Sp, Call("f", u)),
            FormulaBinaryOperator.Add, Call("g", u));
        Formula premises = Conj(Rel(Call("f", D(0)), FormulaRelationOperator.Equal, D(0)),
            All("u", R(), Imp(Rel(D(0), FormulaRelationOperator.LessThanOrEqual, u),
                Call("HasDerivAt", f, rhs, u))),
            All("u", R(), Imp(Pos(u), Pos(Call("g", u)))));
        return Disp(All("f", Seq(R(), Sp, To, Sp, R()),
            All("g", Seq(R(), Sp, To, Sp, R()), All("c", R(), Imp(premises,
            All("t", R(), Imp(Pos(t), Pos(Call("f", t)))))))));
    }
    private static Formula SymmetricFormula()
    {
        Formula v = F.Id("V"), a = F.Id("A"), o = F.Id("o"), y = F.Id("y");
        Formula ell = F.Id("ell"), weights = F.Id("weights"), l = F.Id("L");
        Formula t = F.Id("t"), i = F.Id("i"), j = F.Id("j");
        Formula vector = Seq(v, Sp, To, Sp, R());
        Formula nonneg = Rel(D(0), FormulaRelationOperator.LessThanOrEqual, t);
        Formula uj = Call("eigenvectorUnitary", a, o, j);
        Formula exponential = Call("exp", Sub(D(0), Mul(Call("ell", j), t)));
        Formula sumWeights = Seq(new Formula.Subscript(Sum, Seq(j, Colon, v)), Sp, Call("weights", j));
        Formula sumReturn = Seq(new Formula.Subscript(Sum, Seq(j, Colon, v)), Sp,
            Mul(Call("weights", j), exponential));
        Formula sumCoordinate = Seq(new Formula.Subscript(Sum, Seq(j, Colon, v)), Sp,
            Mul(Mul(Call("eigenvectorUnitary", a, i, j), uj), exponential));
        Formula limits = Exists("L", vector, Conj(
            All("i", v, Call("Tendsto", Call("coordinateCurve", y, i), Call("atTop"), Call("nhds", Call("L", i)))),
            Rel(Call("mulVec", a, l), FormulaRelationOperator.Equal, D(0)),
            Rel(ell, FormulaRelationOperator.Equal, Call("eigenvalues", a)),
            All("j", v, Rel(Call("weights", j), FormulaRelationOperator.Equal,
                new Formula.Power(uj, D(2)))),
            All("t", R(), Imp(nonneg, All("i", v,
                Rel(Call("y", t, i), FormulaRelationOperator.Equal, sumCoordinate))))));
        Formula result = Exists("ell", vector, Exists("weights", vector, Conj(
            All("j", v, And(Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Call("ell", j)),
                Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Call("weights", j)))),
            Rel(sumWeights, FormulaRelationOperator.Equal, D(1)),
            Exists("j", v, Pos(Mul(Call("ell", j), Call("weights", j)))),
            All("t", R(), Imp(nonneg, Rel(Call("y", t, o), FormulaRelationOperator.Equal, sumReturn))),
            All("t", R(), Imp(nonneg, Rel(Call("deriv", Call("coordinateCurve", y, o), t),
                FormulaRelationOperator.LessThan, D(0)))), limits)));
        Formula ode = All("t", R(), Imp(nonneg, All("i", v,
            Call("HasDerivAt", Call("coordinateCurve", y, i),
                Sub(D(0), Call("mulVec", a, Call("curveAt", y, t), i)), t))));
        Formula premises = Conj(Call("PosSemidef", a), Pos(Call("A", o, o)),
            Rel(Call("curveAt", y, D(0)), FormulaRelationOperator.Equal, Call("single", o, D(1))), ode);
        return Disp(All("V", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
            All("A", Call("Matrix", v, v, R()), All("o", v,
            All("y", Seq(R(), Sp, To, Sp, vector), Imp(premises, result)))))));
    }
    private static Formula StationaryFormula(Formula k)
    {
        Formula eq = Call("equilibriumLaw", k), i = F.Id("i");
        Formula v = Call("constant", eq);
        Formula mass = EquilibriumMass(k);
        return And(All("i", Call("Fin", D(5)), Pos(Call("equilibriumLaw", k, i))),
            And(Rel(Seq(new Formula.Subscript(Sum, Seq(i, Colon, Call("Fin", D(5)))),
                Sp, Call("equilibriumLaw", k, i)), FormulaRelationOperator.Equal, D(1)),
            And(Rel(Call("mulVec", Call("generator", k), eq), FormulaRelationOperator.Equal, D(0)),
            And(Rel(Call("association", v, D(0)), FormulaRelationOperator.Equal, D(0)),
            And(Pos(Call("fiberWidth", v, D(0))),
                Rel(Call("activeMass", v, D(0)), FormulaRelationOperator.Equal, mass))))));
    }
    private static Formula EquilibriumMass(Formula k)
    {
        Formula a = Call("a", k), b = Call("b", k), c = Call("c", k), d = Call("d", k);
        Formula theta = Call("theta", k), eta = Call("eta", k);
        return new Formula.Fraction(theta, new Formula.Binary(theta,
            FormulaBinaryOperator.Add, Mul(eta, Mul(new Formula.Fraction(b,
                new Formula.Binary(a, FormulaBinaryOperator.Add, b)),
                new Formula.Fraction(d, new Formula.Binary(c, FormulaBinaryOperator.Add, d))))));
    }
    private static Formula Conj(params Formula[] clauses)
    {
        var result = clauses[clauses.Length - 1];
        for (var n = clauses.Length - 2; n >= 0; n--) result = And(clauses[n], result);
        return result;
    }
    private static Formula SpectralFormula(Formula p)
    {
        Formula j = F.Id("j"), u = F.Id("u");
        Formula ell = Call("ell", j), weight = Call("weights", j);
        Formula modeType = Seq(Call("Fin", D(5)), Sp, To, Sp, R());
        Formula sumWeights = Seq(new Formula.Subscript(Sum, Seq(j, Colon, Call("Fin", D(5)))),
            Sp, weight);
        Formula sumReturn = Seq(new Formula.Subscript(Sum, Seq(j, Colon, Call("Fin", D(5)))),
            Sp, Mul(weight, Call("exp", Sub(D(0), Mul(ell, u)))));
        return Exists("ell", modeType, Exists("weights", modeType, Conj(
            All("j", Call("Fin", D(5)), And(
                Rel(D(0), FormulaRelationOperator.LessThanOrEqual, ell),
                Rel(D(0), FormulaRelationOperator.LessThanOrEqual, weight))),
            Rel(sumWeights, FormulaRelationOperator.Equal, D(1)),
            Exists("j", Call("Fin", D(5)), Pos(Mul(ell, weight))),
            All("u", R(), Imp(Rel(D(0), FormulaRelationOperator.LessThanOrEqual, u),
                Rel(Call("p", u, D(0)), FormulaRelationOperator.Equal, sumReturn))))));
    }
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
        Formula result = Conj(Pos(Call("activeMass", p, t)), Pos(Call("fiberWidth", p, t)),
            Pos(Call("association", p, t)),
            Rel(Mul(Call("p", t, D(2)), Call("p", t, D(3))), FormulaRelationOperator.LessThan,
                Mul(Call("p", t, D(1)), Call("p", t, D(4)))),
            Pos(Sub(Mul(Call("theta", k), Call("p", t, D(0))),
                Mul(Call("eta", k), Call("p", t, D(1))))), SpectralFormula(p),
            All("i", Call("Fin", D(5)), Call("Tendsto", Call("coordinateCurve", p, F.Id("i")),
                F.Id("atTop"), Call("nhds", Call("equilibriumLaw", k, F.Id("i"))))),
            Call("Tendsto", Call("associationCurve", p), F.Id("atTop"), Call("nhds", D(0))),
            Call("Tendsto", Call("activeMassCurve", p), F.Id("atTop"),
                Call("nhds", EquilibriumMass(k))), task);
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
        return Disp(All("k", F.Id("Rates"), And(And(existence, StationaryFormula(k)), All("p", curve,
            Imp(Call("ForwardSolution", k, p), All("t", R(), Imp(Pos(t), result)))))));
    }
}
