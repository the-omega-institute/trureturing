using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.EscapeSpectrum;

internal sealed class FreeUltrafilterChargeCountermodelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.";
    private static readonly LibraryNoteRef Mahon =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/mahon2026ultrafilter");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula NNReal => Call("NNReal");
    private static Formula BoolType => Call("Bool");
    private static Formula X => F.Id("X");
    private static Formula Pair => Seq(X, Sp, Times, Sp, X);
    private static Formula U => F.Id("U");
    private static Formula E => F.Id("E");
    private static Formula B => F.Id("B");
    private static Formula Q => F.Id("q");
    private static Formula Target => F.Id("T");
    private static Formula Definitions => F.Id("d");
    private static Formula Cost => F.Id("c");
    private static Formula Weight => F.Id("w");
    private static Formula Residual => F.Id("R");
    private static Formula Prefixes => F.Id("F");
    private static Formula Chain => F.Id("A");
    private static Formula Edge => F.Id("e");
    private static Formula False => Call("false");
    private static Formula True => Call("true");
    private static Formula SetOf(Formula type) => Call("Set", type);
    private static Formula App(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula And(Formula body) => Seq(Open, body, Close, Sp, Land);
    private static Formula Implies(Formula premise, Formula result) =>
        Seq(Open, premise, Close, Sp, Rightarrow, Sp, result);
    private static Formula EdgeAt(Formula sign) => App(Edge, sign);
    private static Formula Pullback(Formula sign, Formula set) =>
        Call("preimage", EdgeAt(sign), set);
    private static Formula Average(Formula set) => Seq(
        Frac, Grp(D(1)), Grp(D(2)), Sp, App(Mu, Pullback(False, set)), Sp, Plus, Sp,
        Frac, Grp(D(1)), Grp(D(2)), Sp, App(Mu, Pullback(True, set)));
    private static Formula Tail(Formula n) => Call("Ioi", n);
    private static Formula BothTails(Formula n) => Seq(
        Call("image", EdgeAt(False), Tail(n)), Sp, Cup, Sp,
        Call("image", EdgeAt(True), Tail(n)));
    private static Formula Mass(Formula s) => Call(
        "finiteResidualMass", Gamma, Definitions, Q, Target, Weight, s);
    private static Formula Values(Formula l) => Call(
        "finiteBudgetMassValues", Gamma, Definitions, Q, Target, Cost, Weight, l);
    private static Formula Spectrum(Formula l) => Call(
        "finiteEscapeSpectrum", Gamma, Definitions, Q, Target, Cost, Weight, l);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A free ultrafilter gives full residual mass at every finite budget, "
            + "although the common blind residual is empty.",
        H("Free Ultrafilter Charge Countermodel"),
        Blocks(
            Claim("two-edge-content", "edgeCharge", "The two-sign full-powerset charge",
                ObjectsFormula(),
                "The state space is the natural numbers times Bool, with false and true "
                    + "representing the two signs. The base readout forgets the sign and "
                    + "the target reads it. Only positive cutoffs belong to the language. "
                    + "The charge is defined on every set of pairs; its restriction to P(E) "
                    + "is the source charge. The real weight is the coercion of this AddContent.",
                DescribeRole.Definition),
            Claim("scalar-membership", "mu_formula", "The scalar membership formula",
                ScalarFormula(),
                "The ENNReal membership charge has only values zero and one. Its "
                    + "finite-valued conversion to NNReal therefore has the displayed "
                    + "formula. Disjoint additivity is inherited from the ultrafilter "
                    + "charge through toNNReal_add. The chosen ultrafilter is hyperfilter Nat.",
                DescribeRole.Theorem),
            Claim("finite-tail-preimage", "residual_edge_preimage",
                "Every finite selected residual contains a tail", WitnessFormula(),
                "The canonical residual decomposition makes an edge survive precisely "
                    + "when its index exceeds every selected cutoff. The empty selection "
                    + "gives the whole natural-number preimage. For any finite selection, "
                    + "the tail above its largest cutoff belongs to the free ultrafilter; "
                    + "both signs consequently have scalar mass one.", DescribeRole.Theorem),
            Claim("affordable-mass-values", "finite_budget_values_eq_singleton",
                "All affordable masses equal one", BudgetFormula(),
                "The cost of a finite selection is its cardinality as a real number. "
                    + "The empty selection has cost zero and is affordable at every "
                    + "NNReal budget, including zero. Thus the set whose infimum defines "
                    + "the canonical budget envelope is exactly the singleton one.",
                DescribeRole.Theorem),
            Claim("free-ultrafilter-countermodel", "free_ultrafilter_charge_countermodel",
                "Finite escape persists without decreasing-chain continuity", FullFormula(),
                "The positive cutoffs are distinct definitions and form a countable "
                    + "nonempty language with unit costs. Each actual residual edge is "
                    + "eventually separated, so the common blind residual is empty. "
                    + "The exhausting initial segments leave exactly the two tails shown. "
                    + "Their antitone residual chain has empty intersection but constant "
                    + "mass one, whereas the empty set has mass zero. Normalization by "
                    + "the baseline mass one makes every finite nonnegative budget's "
                    + "canonical spectrum equal one. The standard classical hyperfilter "
                    + "construction supplies the free ultrafilter; no additional existence "
                    + "or continuity hypothesis is assumed.", DescribeRole.Theorem))));

    private static DocumentBlock Claim(
        string id, string declaration, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Mahon),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula ObjectsFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), i = F.Id("i"), j = F.Id("j");
        Formula s = F.Id("S"), c = F.Id("C"), b = F.Id("b");
        Formula point = Seq(Open, k, Comma, i, Close);
        Formula family = Seq(i, Colon, Sp, Gamma, Sp, Mapsto, Sp,
            App(Definitions, Call("val", i)));
        return Disp(new Formula.Aligned([
            Equal(X, Seq(N, Sp, Times, Sp, BoolType)),
            Seq(Q, Colon, Sp, X, Sp, To, Sp, N, Comma, Sp,
                Target, Colon, Sp, X, Sp, To, Sp, BoolType),
            All(k, N, All(i, BoolType, Equal(App(Q, point), k))),
            All(k, N, All(i, BoolType, Equal(App(Target, point), i))),
            Equal(Gamma, Call("setOf", Seq(n, Colon, Sp, N), Seq(D(1), Sp, Leq, Sp, n))),
            Seq(Definitions, Colon, Sp, N, Sp, To, Sp, X, Sp, To, Sp, BoolType),
            All(n, N, All(k, N, All(i, BoolType, Equal(App(App(Definitions, n), point),
                Call("ite", Seq(k, Sp, Leq, Sp, n), i, False))))),
            Seq(Cost, Colon, Sp, N, Sp, To, Sp, Real),
            All(n, N, Equal(App(Cost, n), D(1))),
            Seq(Edge, Colon, Sp, BoolType, Sp, To, Sp, N, Sp, To, Sp, Pair),
            All(b, BoolType, All(k, N, Equal(App(EdgeAt(b), k), Seq(Open,
                Open, k, Comma, b, Close, Comma,
                Open, k, Comma, Call("BoolNot", b), Close, Close)))),
            Equal(E, Call("defectRelation", Q, Target)),
            Equal(U, Call("hyperfilter", N)),
            Seq(Mu, Colon, Sp, SetOf(N), Sp, To, Sp, NNReal),
            All(c, SetOf(N), Equal(App(Mu, c), Call("toNNReal", Call("ultrafilterCharge", U, c)))),
            Seq(Nu, Colon, Sp, Call("AddContent", NNReal,
                Seq(Call("univ"), Colon, Sp, SetOf(SetOf(Pair))))),
            All(c, SetOf(Pair), Equal(App(Nu, c), Average(c))),
            Seq(Weight, Colon, Sp, Call("EscapeWeight", Pair)),
            All(c, SetOf(Pair), Equal(Call("mass", Weight, c), Call("coeReal", App(Nu, c)))),
            All(s, Call("Finset", Gamma), Equal(App(Residual, s), Call("defectRelation",
                Call("conceptJoin", Q,
                    Call("finiteSelectionSupplement", Gamma, Definitions, s)), Target))),
            Equal(B, Call("intersection", E, Call("jointKernel", family))),
            All(n, N, Equal(App(Prefixes, n), Call("FinsetImage",
                Seq(j, Sp, Mapsto, Sp, Call("subtype", Seq(j, Sp, Plus, Sp, D(1)), Gamma)),
                Call("FinsetRange", n)))),
            All(n, N, Equal(App(Chain, n),
                App(Residual, App(Prefixes, Seq(n, Sp, Plus, Sp, D(1)))))),
        ]));
    }

    private static Formula ScalarFormula()
    {
        Formula c = F.Id("C");
        return Disp(All(c, SetOf(N), Equal(App(Mu, c),
            Call("ite", Member(c, U), D(1), D(0)))));
    }

    private static Formula WitnessFormula()
    {
        Formula s = F.Id("S"), b = F.Id("b"), k = F.Id("k"), j = F.Id("j");
        return Disp(All(s, Call("Finset", Gamma), All(b, BoolType,
            Equal(Pullback(b, App(Residual, s)),
                Call("setOf", Seq(k, Colon, Sp, N), All(j, Gamma,
                    Implies(Member(j, s), Seq(Call("val", j), Sp, Lt, Sp, k))))))));
    }

    private static Formula BudgetFormula()
    {
        Formula l = F.Id("L");
        return Disp(All(l, NNReal, Equal(Values(l), Call("singleton", D(1)))));
    }

    private static Formula FullFormula()
    {
        Formula i = F.Id("i"), s = F.Id("S"), c = F.Id("C"), d = F.Id("D");
        Formula n = F.Id("n"), l = F.Id("L");
        Formula family = Seq(i, Colon, Sp, Gamma, Sp, Mapsto, Sp,
            App(Definitions, Call("val", i)));
        Formula next = Seq(n, Sp, Plus, Sp, D(1));
        Formula chainMass = Seq(n, Colon, Sp, N, Sp, Mapsto, Sp,
            Call("coeReal", App(Nu, App(Chain, n))));
        return Disp(new Formula.Aligned([
            And(Call("Countable", Gamma)), And(Call("Nonempty", Gamma)),
            And(Call("Injective", family)),
            And(All(i, N, Implies(Member(i, Gamma), Seq(D(0), Sp, Lt, Sp, App(Cost, i))))),
            And(All(s, Call("Finset", Gamma), Equal(
                Call("finiteSelectionCost", Gamma, Cost, s), Call("coeReal", Call("card", s))))),
            And(Equal(E, Seq(Call("range", EdgeAt(False)), Sp, Cup, Sp,
                Call("range", EdgeAt(True))))),
            And(Seq(Call("toFilter", U), Sp, Leq, Sp, Call("cofinite", N))),
            And(All(c, SetOf(N), Implies(Call("Finite", c), Seq(Neg, Sp, Open, Member(c, U), Close)))),
            And(All(c, SetOf(N), Equal(App(Mu, c), Call("ite", Member(c, U), D(1), D(0))))),
            And(All(c, SetOf(Pair), Equal(App(Nu, c), Average(c)))),
            And(All(c, SetOf(Pair), Equal(App(Nu, c), App(Nu, Call("intersection", c, E))))),
            And(Equal(App(Nu, Emptyset), D(0))),
            And(Call("Monotone", Seq(c, Colon, Sp, SetOf(Pair), Sp, Mapsto, Sp, App(Nu, c)))),
            And(All(c, SetOf(Pair), Seq(D(0), Sp, Leq, Sp, Call("coeReal", App(Nu, c))))),
            And(All(c, SetOf(Pair), All(d, SetOf(Pair), Implies(Call("Disjoint", c, d),
                Equal(App(Nu, Seq(c, Sp, Cup, Sp, d)),
                    Seq(App(Nu, c), Sp, Plus, Sp, App(Nu, d))))))),
            And(Equal(App(Nu, E), D(1))), And(Equal(B, Emptyset)),
            And(All(s, Call("Finset", Gamma), Equal(Mass(s), D(1)))),
            And(All(n, N, Implies(Seq(D(1), Sp, Leq, Sp, n),
                Equal(App(Residual, App(Prefixes, n)), BothTails(n))))),
            And(Call("Monotone", Prefixes)),
            And(All(i, Gamma, Seq(Exists, Sp, n, Colon, Sp, N, Comma, Sp,
                Member(i, App(Prefixes, next))))),
            And(Call("Antitone", Chain)),
            And(Equal(Call("iInter", Seq(n, Colon, Sp, N), App(Chain, n)), Emptyset)),
            And(Seq(Neg, Sp, Call("Tendsto", chainMass, Call("atTop"),
                Call("nhds", Call("coeReal", App(Nu, Emptyset)))))),
            Seq(All(l, NNReal, Equal(Spectrum(l), D(1))), Dot),
        ]));
    }
}
