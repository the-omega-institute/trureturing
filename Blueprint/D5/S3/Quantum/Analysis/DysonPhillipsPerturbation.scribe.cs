using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class DysonPhillipsPerturbationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Dyson–Phillips series constructs the unique strongly continuous bounded-perturbation evolution on every complex Banach space.",
        H("Dyson–Phillips bounded perturbation"), Blocks(
            Paragraph(Text("Fix any universe u, a type E in Type u, a normed additive commutative group structure on E, a complex normed-space structure and completeness. All integrals are E-valued Bochner interval integrals with real Lebesgue measure volume. Let S be a family of continuous complex linear endomorphisms indexed by all real times, equal to the identity at nonpositive times, multiplicative at nonnegative times, of operator norm at most one at every real time, and with continuous vector orbits. Let B be any continuous complex linear endomorphism. There is no nontriviality assumption on E.")),
            Paragraph(Text("The public dysonTerm definition is the following actual ordered recurrence. The order of S and B is retained; no commutativity is assumed. The public dysonSum is the sum of these terms at the clamped time max(t,0).")),
            new DocumentBlock.DisplayFormula(Definitions()),
            Describe.Lean(
                DescribeId.Create("bounded-perturbation"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/DysonPhillipsPerturbation.bounded_perturbation"),
                H("Construction, estimates and complete Volterra uniqueness"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/engelnagel2000boundedperturbation")),
                Blocks(
                    Paragraph(Text("For every natural index n, every nonnegative time t and every x in E, the actual term has norm at most (norm(B)*t)^n/n! times norm(x), and the E-valued series is summable. A single family U of continuous complex linear maps has identity values at every nonpositive time, continuous vector orbits on the entire real line, and the Duhamel equation at every nonnegative time.")),
                    Paragraph(Text("Uniqueness compares U with every family V of continuous complex linear maps satisfying only these three conditions: nonpositive identity, continuous vector orbits and Duhamel. The competitor is not required to satisfy a series representation, a growth bound or a composition law. The same U has the displayed clamped series formula, the nonnegative-time semigroup law and the exponential operator-norm bound for every real time.")),
                    Paragraph(Text("For every real horizon T, every function X from the reals to E that is continuous on Icc(0,T), and every initial vector x, the Duhamel identity restricted to that interval implies X(t)=U(t)x throughout that interval. No continuity off the interval or differentiability of X is required. Negative T gives the empty interval and a vacuous conclusion. Zero time, zero B, zero x and the zero Banach space are all included; no use of norm(identity)=1 is needed.")),
                    Paragraph(Text("The proof uses the native real-linear NNReal contraction-semigroup bundle only for its action continuity and contraction estimate. Its operator at q is S(q) restricted from complex to real scalars. Pulling back along Real.toNNReal recovers S at all real times by the nonpositive identity assumption. Every E-valued integral and every complex-homogeneity argument still uses the original complex S and B.")),
                    Paragraph(Text("Induction integrates the preceding factorial majorant against the actual Banach kernel. Uniform convergence on bounded time intervals gives continuous orbits. Dominated summation under the Bochner integral gives Duhamel. For two continuous solutions on a closed interval, their difference Y obeys the homogeneous Volterra equation. A compact-interval bound M iterates to norm(Y(t))<=M*(norm(B)*t)^n/n! for every n, and the factorial limit forces Y(t)=0. Splitting a shifted Duhamel integral and applying this curve uniqueness gives composition.")),
                    Paragraph(Text("A restricted application uses S equal to a supplied native free contraction family and B=M, or B=g*W for a bounded multiplier W. The recurrence is then exactly the ordered free-evolution/multiplier kernel. A supplied norm(M)<=P transfers the factorial estimate to (P*t)^n/n!. Identifying that family with a particular unbounded-generator heat evolution, proving preservation of a positive cone, and proving quadrature or ground-state error estimates require their own hypotheses and bridges. The theorem supplies the general Volterra construction; it makes none of those identifications.")),
                    Paragraph(Text("This is the classical Dyson–Phillips bounded-perturbation result, supported by Engel–Nagel III.1 and Schnaubelt Theorem 3.4. The selected proof adapts Zayn Blore's Apache-2.0 source at revision ca3edfd7a5576d6c4e188501f9abb7c3f38ccd7f; the owning literature note records the exact path, license and adoption-based retirement condition. No generator or domain, bounded generator, operator-norm continuity, inverse, dissipativity or contractivity of U is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Real => Call("Real");
    private static Formula Nat => Call("Nat");
    private static Formula E => F.Id("E");
    private static Formula S => F.Id("S");
    private static Formula B => F.Id("B");
    private static Formula Zero => new Formula.Number(0);
    private static Formula One => new Formula.Number(1);
    private static Formula Clm => Call("ComplexCLM", E, E);
    private static Formula Family => new Formula.TypeArrow(Real, Clm);
    private static Formula All(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Some(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Lam(string n, Formula d, Formula b) =>
        Seq(Grp(F.Id(n), Colon, d), Mapsto, Sp, b);
    private static Formula Norm(Formula f) => new Formula.Norm(f);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Conj(params Formula[] fs)
    {
        Formula r = fs[^1];
        for (int i = fs.Length - 2; i >= 0; --i)
            r = new Formula.Logic(fs[i], FormulaLogicOperator.And, r);
        return r;
    }
    private static Formula Scope(Formula body) =>
        All("u", Call("Universe"), All("E", Call("Type", F.Id("u")),
        All("addGroup", Call("NormedAddCommGroup", E),
        All("complexSpace", Call("NormedSpace", Call("Complex"), E),
        All("complete", Call("CompleteSpace", E), All("S", Family, All("B", Clm, body)))))));
    private static Formula Term(Formula n, Formula t, Formula x) => Call("dysonTerm", S, B, n, t, x);
    private static Formula Integral(Formula t, Formula values) => Call("intervalIntegral",
        Call("volume"), Zero, t, Lam("r", Real,
            At(At(S, Subtract(t, F.Id("r"))), At(B, values))));
    private static Formula Conditions(Formula family) => Conj(
        All("t", Real, Imp(Le(F.Id("t"), Zero), Equal(At(family, F.Id("t")), Call("id", Call("Complex"), E)))),
        All("x", E, Call("Continuous", Lam("t", Real, At(At(family, F.Id("t")), F.Id("x"))))),
        All("t", Real, Imp(Le(Zero, F.Id("t")), All("x", E,
            Equal(At(At(family, F.Id("t")), F.Id("x")), Add(At(At(S, F.Id("t")), F.Id("x")),
                Integral(F.Id("t"), At(At(family, F.Id("r")), F.Id("x")))))))));
    private static Formula Input() => Conj(
        All("t", Real, Imp(Le(F.Id("t"), Zero), Equal(At(S, F.Id("t")), Call("id", Call("Complex"), E)))),
        All("s", Real, All("t", Real, Imp(Conj(Le(Zero, F.Id("s")), Le(Zero, F.Id("t"))),
            Equal(At(S, Add(F.Id("s"), F.Id("t"))), Call("comp", At(S, F.Id("s")), At(S, F.Id("t"))))))),
        All("t", Real, Le(Norm(At(S, F.Id("t"))), One)),
        All("x", E, Call("Continuous", Lam("t", Real, At(At(S, F.Id("t")), F.Id("x"))))));
    private static Formula Definitions()
    {
        Formula n=F.Id("n"), t=F.Id("t"), x=F.Id("x");
        return Scope(All("n", Nat, All("t", Real, All("x", E, Conj(
            Equal(Term(Zero,t,x), At(At(S,t),x)),
            Equal(Term(Add(n,One),t,x), Integral(t, Term(n,F.Id("r"),x))),
            Equal(Call("dysonSum",S,B,t,x), Call("tsum", Lam("n",Nat,Term(n,Call("max",t,Zero),x)))))))));
    }
    private static Formula Statement()
    {
        Formula n=F.Id("n"), t=F.Id("t"), x=F.Id("x"), u=F.Id("U"), v=F.Id("V");
        Formula majorant=Multiply(new Formula.Fraction(new Formula.Power(Multiply(Norm(B),t),n),
            Call("factorial",n)),Norm(x));
        Formula bound=All("n",Nat,All("t",Real,Imp(Le(Zero,t),All("x",E,Le(Norm(Term(n,t,x)),majorant)))));
        Formula summable=All("t",Real,Imp(Le(Zero,t),All("x",E,Call("Summable",Lam("n",Nat,Term(n,t,x))))));
        Formula series=All("t",Real,All("x",E,Equal(At(At(u,t),x),
            Call("tsum",Lam("n",Nat,Term(n,Call("max",t,Zero),x))))));
        Formula composition=All("s",Real,All("t",Real,Imp(Conj(Le(Zero,F.Id("s")),Le(Zero,t)),
            Equal(At(u,Add(F.Id("s"),t)),Call("comp",At(u,F.Id("s")),At(u,t))))));
        Formula growth=All("t",Real,Le(Norm(At(u,t)),Call("exp",Multiply(Norm(B),Call("max",t,Zero)))));
        Formula interval=Call("Icc",Zero,F.Id("T"));
        Formula equation=All("t",interval,Equal(At(F.Id("X"),t),
            Add(At(At(S,t),x),Integral(t,At(F.Id("X"),F.Id("r"))))));
        Formula curves=All("T",Real,All("X",new Formula.TypeArrow(Real,E),All("x",E,
            Imp(Conj(Call("ContinuousOn",F.Id("X"),interval),equation),
                All("t",interval,Equal(At(F.Id("X"),t),At(At(u,t),x)))))));
        return Scope(Imp(Input(),Conj(bound,summable,Some("U",Family,Conj(Conditions(u),
            All("V",Family,Imp(Conditions(v),Equal(v,u))),series,composition,growth,curves)))));
    }
}
