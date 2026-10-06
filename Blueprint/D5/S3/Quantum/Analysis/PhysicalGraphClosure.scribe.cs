using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;
internal sealed class PhysicalGraphClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact physical Hermite basis identifies the actual oscillator weak graph and closure.",
        H("Conditional Physical Oscillator Graph"),
        Blocks(Describe.Lean(
            DescribeId.Create("physical-oscillator-actual-graph-closure"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/PhysicalGraphClosure.physical_graph_closure"),
            H("Actual graph, Schwartz joining and nonnegative finite core"),
            StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every natural dimension d, positive hbar, positive coordinate masses "
                    + "m and frequencies omega, take Schwartz representatives phi indexed by alpha in "
                    + "Fin d to Nat with pointwise values exactly Phi from PhysicalHermiteTests. The "
                    + "separate input e is a Hilbert basis of the actual complex Lebesgue L2 on "
                    + "EuclideanSpace R (Fin d), with e of alpha exactly J phi of alpha.")),
                Paragraph(Text("S acts by the actual sum of second coordinate derivatives and quadratic "
                    + "potentials on every Schwartz class. C is the finite complex physical Hermite span, "
                    + "T is S restricted to C, K is the genuine closure of T, and E is the sum of hbar "
                    + "times omega of j times alpha of j plus one half. S is contained in K, is closable, "
                    + "and its closure and adjoint equal K. K is self-adjoint, closed and nonnegative, "
                    + "and C is a core of K.")),
                Paragraph(Text("For every pair f and g, compact smooth Weak tests of the full differential "
                    + "sum are equivalent to the actual K graph and to c of alpha of g equals E of alpha "
                    + "times c of alpha of f. The domain is exactly square-summability of the weighted "
                    + "coefficients. The same finite sets give actual T-domain sums converging to f and "
                    + "their images converging to g.")),
                Paragraph(Text("Physical differential action identifies the finite restriction. Schwartz "
                    + "symmetry gives coefficients on the adjoint graph, while closed extension and "
                    + "genuine graph closure give the reverse inclusion. On simultaneous finite graph "
                    + "approximants the real quadratic form is a sum of nonnegative energies times "
                    + "squared coefficient norms. Inner-product continuity passes nonnegativity to K.")),
                Paragraph(Text("Dimension zero and zero energy remain in scope. There is no division by "
                    + "energy and no separate derivative or potential L2 assumption on f. The theorem "
                    + "is conditional on the exactly identified physical Hilbert basis; physical "
                    + "orthonormality and totality remain separate obligations. Imported constructions "
                    + "retain their PhysLean, Timepiece and W21 license and NOTICE chains."))),
            DescribeRole.Theorem))));
    private static Formula And(params Formula[] xs) => xs.Aggregate((a, b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(n), t)], b);
    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), h = F.Id("hbar"), m = F.Id("m"), w = F.Id("omega");
        Formula a = F.Id("alpha"), j = F.Id("j"), x = F.Id("x"), p = F.Id("phi"), e = F.Id("e");
        Formula f = F.Id("f"), g = F.Id("g"), u = F.Id("u"), v = F.Id("v"), fs = F.Id("F");
        Formula r = Seq(Mathbb, Grp(F.Id("R"))), c = Seq(Mathbb, Grp(F.Id("C")));
        Formula i = Call("Fin", d), ix = new Formula.TypeArrow(i, F.Id("Nat"));
        Formula space = Call("EuclideanSpace", r, i), sch = Call("Schwartz", space, c);
        Formula hil = Call("Lp", c, D(2), Call("volume", space));
        Formula pa = new Formula.Apply(p, [a]), ea = new Formula.Apply(e, [a]);
        Formula en = Call("E", d, h, w, a), s = Call("S", d, h, m, w);
        Formula core = Call("span", c, Call("range", e)), t = Call("domRestrict", s, core);
        Formula k = Call("closure", t), graph = Call("graph", k);
        Formula pair = Call("Pair", f, g), member = Call("Member", pair, graph);
        Formula cf = Call("inner", ea, f), cg = Call("inner", ea, g);
        Formula uf = new Formula.Apply(u, [fs]), fin = Call("Finset", ix);
        Formula approx = new Formula.BindMany(FormulaQuantifier.Exists,
            [new(FormulaIdentifier.Create("u"), new Formula.TypeArrow(fin, Call("domain", t)))],
            And(All("F", fin, Equal(uf, Call("sum", new Formula.Sequence(Call("mul", cf, ea), a, fs)))),
                All("F", fin, Equal(Call("apply", t, uf), Call("sum", new Formula.Sequence(Call("mul", en, cf, ea), a, fs)))),
                Call("Tendsto", new Formula.Sequence(uf, fs, fin), F.Id("atTop"), Call("nhds", f)),
                Call("Tendsto", new Formula.Sequence(Call("apply", t, uf), fs, fin), F.Id("atTop"), Call("nhds", g))));
        Formula fg = And(new Formula.Logic(Call("Weak", d, h, m, w, f, g), FormulaLogicOperator.Iff, member),
            new Formula.Logic(member, FormulaLogicOperator.Iff, All("alpha", ix, Equal(cg, Call("mul", en, cf)))),
            new Formula.Logic(Call("Member", f, Call("domain", k)), FormulaLogicOperator.Iff,
                Call("MemL2", new Formula.Sequence(Call("mul", en, cf), a, ix))),
            new Formula.Logic(member, FormulaLogicOperator.Implies, approx));
        Formula result = And(Le(s, k), Call("IsClosable", s), Equal(Call("closure", s), k),
            Equal(Call("adjoint", s), k), Call("IsSelfAdjoint", k), Call("IsClosed", k), Call("HasCore", k, core),
            All("v", Call("domain", k), Le(D(0), Call("Re", Call("inner", v, Call("apply", k, v))))),
            All("f", hil, All("g", hil, fg)));
        Formula hyp = And(Lt(D(0), h), All("j", i, Lt(D(0), new Formula.Apply(m, [j]))),
            All("j", i, Lt(D(0), new Formula.Apply(w, [j]))),
            All("alpha", ix, All("x", space, Equal(new Formula.Apply(pa, [x]), Call("Phi", d, h, m, w, a, x)))),
            All("alpha", ix, Equal(ea, Call("J", pa))));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("d"), F.Id("Nat")), new(FormulaIdentifier.Create("hbar"), r),
             new(FormulaIdentifier.Create("m"), new Formula.TypeArrow(i, r)),
             new(FormulaIdentifier.Create("omega"), new Formula.TypeArrow(i, r)),
             new(FormulaIdentifier.Create("phi"), new Formula.TypeArrow(ix, sch)),
             new(FormulaIdentifier.Create("e"), Call("HilbertBasis", ix, c, hil))],
            new Formula.Logic(hyp, FormulaLogicOperator.Implies, result));
    }
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
}
