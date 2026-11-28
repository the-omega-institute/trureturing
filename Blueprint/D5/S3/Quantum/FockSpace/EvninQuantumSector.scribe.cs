using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FockSpace;

internal sealed class EvninQuantumSectorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/FockSpace/EvninQuantumSector";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/evnin2026quantumestimates");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Evnin's normally ordered resonant Hamiltonian has greatest real spectral value "
        + "(N − 1)(N + 2σM)/2 in every nonempty sector for every real σ ≥ 1.",
        H("The exact top eigenvalue in Evnin's finite sectors"),
        Blocks(
            Definition("modes", "Mode", "Ambient modes", ModeBody(),
                "The natural number L is the largest ambient mode label. A value of Fin(L + 1) "
                + "has a natural label from 0 through L."),
            Definition("sector", "Sector", "Fixed particle number and momentum", SectorBody(),
                "The sector is a subtype of occupation functions on Mode(L). The first sum fixes particle "
                + "number and the second fixes momentum using the natural mode labels. The Hamiltonian "
                + "acts on Sector(M, N, M) in the normalized bosonic basis of Eq. (22)."),
            Definition("finite-sector", "instFintypeSector", "Finite occupation sectors",
                SectorInstance("instFintypeSector", "Fintype"),
                "The Fintype instance uses Fintype.ofInjective on the map that sends each occupation "
                + "to its coordinate function into Fin(N + 1). Each occupation is at most its total N, "
                + "and equality of the bounded functions gives equality of the occupations."),
            Definition("sector-equality", "instDecidableEqSector", "Decidable sector equality",
                SectorInstance("instDecidableEqSector", "DecidableEq"),
                "The equality instance is Classical.decEq on Sector(L, N, M)."),
            Definition("raney", "raney", "Raney coefficients", RaneyBody(),
                "Equation (31) gives this Gamma quotient with real parameters s and r and natural index j. "
                + "Mathlib assigns Gamma(0) = 0 at the pole and uses total division. The proof uses s ≥ 1 "
                + "and r > 0, so all Gamma arguments are positive. It uses r = 1 for the Hamiltonian "
                + "and eigenvector and r = 2 in the convolution."),
            Definition("energy", "energy", "Energy of the attaining state", EnergyBody(),
                "Both N and M are cast from natural numbers to real numbers before the arithmetic of Eq. (33)."),
            Definition("vector", "occupationVector", "Factorial occupation vector", VectorBody(),
                "For real mode weights A, each coordinate is computed in the reals and cast to the complex "
                + "numbers. Mathlib's real square root is zero for negative arguments. In the theorem, "
                + "the weights A(t) = raney(s, 1, t) are positive for every natural label t, and the vector "
                + "is indexed by Sector(M, N, M)."),
            Definition("hamiltonian", "hamiltonian", "Normally ordered Hamiltonian", HamiltonianBody(),
                "For N at least two, B is the ordered pair annihilation matrix. Angle brackets denote "
                + "the element of Mode(M) with the indicated natural label. The bracketed equalities "
                + "in the entry formula are indicators, with value one when true and zero otherwise. "
                + "The adjoint is conjugate transpose, and smul is the real scalar action on complex matrices. "
                + "The momentum constraint forces all modes above M to have zero occupation. A pair "
                + "with total momentum above M cannot be removed. Both orders of a distinct-mode pair "
                + "occur in the sums from Eqs. (19) and (30)."),
            Describe.Lean(
                DescribeId.Create("evnin-quantum-sector-claim"), DeclarationHandle.Create(Module + ".claim"),
                H("Proposition on the top spectral value"),
                StatementSource.FromAuthor(Disp(ClaimBody(includeClaimName: true))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write s for σ. The assertion ranges over nonempty sectors, including the one-particle "
                        + "sectors and the vacuum of zero momentum. Greatest means that the energy belongs to "
                        + "the real spectrum and is an upper bound for it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("evnin-quantum-sector-top-eigenvalue"),
                DeclarationHandle.Create(Module + ".top_finite_sector_eigenvalue"),
                H("Spectral bound and attainment"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Each pair annihilator gives a diagonal matrix when multiplied by its adjoint "
                        + "on the left. Each removable column has exactly one lower occupation, and distinct "
                        + "columns cannot share that row. An impossible removal contributes zero, including "
                        + "when the lower sector is empty. Summing the ordered diagonal counts gives N(N − 1), "
                        + "and weighting by pair momentum gives 2M(N − 1). Thus half the sum with block weights "
                        + "1 + σj is E times the identity.")),
                    Paragraph(Text(
                        "Lagrange–Bürmann applied to the formal solution T of T = X(1 + T)^σ identifies the "
                        + "coefficients of (1 + T)^r for r = 1, 2 with the Gamma quotients of Eq. (31). "
                        + "The Cauchy product and the Gamma recurrence give cⱼ times the sum of wⱼₖ squared "
                        + "equal to 1 + σj. Expanding the weighted Gram identity writes E times the identity "
                        + "minus H as a sum of adjoint squares with weights cⱼ/4. Its pair differences are "
                        + "wⱼₖ times the lth pair minus wⱼₗ times the kth pair. Each coefficient is nonnegative, "
                        + "so the real spectrum is bounded above by E.")),
                    Paragraph(Text(
                        "Adding one particle replaces its factorial by the next factorial. The square-root "
                        + "ratio cancels the coefficient of the corresponding annihilator. Applying this "
                        + "twice gives wⱼₖ times the same lower-sector vector for every kth pair, including "
                        + "a repeated mode. Every difference therefore kills v. All its coordinates are "
                        + "positive before casting to complex numbers, so v is nonzero in every nonempty "
                        + "sector. This gives the eigenvalue E and proves attainment. With fewer than two "
                        + "particles the nonempty sectors have zero energy."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("evnin-2026-quantum-sector-maximum"), ResolutionKind.Proved)))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, Formula body, string explanation) => Describe.Lean(
            DescribeId.Create("evnin-quantum-sector-" + id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(body)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static Formula SectorInstance(string declaration, string type)
    {
        Formula l = F.Id("L"), n = F.Id("N"), m = F.Id("M");
        return Quantify(Typed(Call(declaration, l, n, m), Call(type, Call("Sector", l, n, m))),
            Typed(l, Naturals()), Typed(n, Naturals()), Typed(m, Naturals()));
    }

    private static Formula ModeBody()
    {
        Formula cutoff = F.Id("L");
        return Quantify(Equal(Call("Mode", cutoff), Call("Fin", Add(cutoff, D(1)))),
            Typed(cutoff, Naturals()));
    }

    private static Formula SectorBody()
    {
        Formula cutoff = F.Id("L"), particles = F.Id("N"), momentum = F.Id("M");
        Formula eta = F.Id("eta"), mode = F.Id("i"), modes = Call("Mode", cutoff);
        Formula occupation = new Formula.Apply(eta, [mode]);
        Formula domain = new Formula.TypeArrow(modes, Naturals());
        Formula count = Equal(Indexed(Sum, mode, modes, occupation), particles);
        Formula weight = Equal(Indexed(Sum, mode, modes, Mul(Call("val", mode), occupation)), momentum);
        Formula subtype = Seq(OpenBrace, eta, Colon, Sp, domain, Sp, Mid, Sp, And(count, weight), CloseBrace);
        return Quantify(Equal(Call("Sector", cutoff, particles, momentum), subtype),
            Typed(cutoff, Naturals()), Typed(particles, Naturals()), Typed(momentum, Naturals()));
    }

    private static Formula RaneyBody()
    {
        Formula s = F.Id("s"), r = F.Id("r"), j = F.Id("j");
        Formula index = RealCast(j);
        Formula numerator = Mul(r, new Formula.Apply(Gamma, [Add(Mul(s, index), r)]));
        Formula first = new Formula.Apply(Gamma, [Add(Add(Mul(Sub(s, D(1)), index), r), D(1))]);
        Formula second = new Formula.Apply(Gamma, [Add(index, D(1))]);
        return Quantify(Equal(Call("raney", s, r, j), new Formula.Fraction(numerator, Mul(first, second))),
            Typed(s, Reals()), Typed(r, Reals()), Typed(j, Naturals()));
    }

    private static Formula EnergyBody()
    {
        Formula s = F.Id("s"), n = F.Id("N"), m = F.Id("M");
        Formula particles = RealCast(n), momentum = RealCast(m);
        Formula value = new Formula.Fraction(
            Mul(Sub(particles, D(1)), Add(particles, Mul(Mul(D(2), s), momentum))), D(2));
        return Quantify(Equal(Call("energy", s, n, m), value),
            Typed(s, Reals()), Typed(n, Naturals()), Typed(m, Naturals()));
    }

    private static Formula VectorBody()
    {
        Formula l = F.Id("L"), n = F.Id("N"), m = F.Id("M");
        Formula a = F.Id("A"), i = F.Id("i"), eta = F.Id("eta");
        Formula occupation = Occupation(eta, i);
        Formula weight = new Formula.Apply(a, [Call("val", i)]);
        Formula factorial = Seq(Parenthesized(occupation), Bang);
        Formula amplitude = new Formula.Fraction(new Formula.Power(Root(weight), occupation), Root(RealCast(factorial)));
        Formula product = Indexed(Prod, i, Call("Mode", l), amplitude);
        return Quantify(Equal(Call("occupationVector", a, eta), OfReal(product)),
            Typed(l, Naturals()), Typed(n, Naturals()), Typed(m, Naturals()),
            Typed(a, new Formula.TypeArrow(Naturals(), Reals())), Typed(eta, Call("Sector", l, n, m)));
    }

    private static Formula HamiltonianBody()
    {
        Formula s = F.Id("s"), n = F.Id("N"), m = F.Id("M");
        Formula t = F.Id("t"), j = F.Id("j"), k = F.Id("k"), l = F.Id("l");
        Formula a = F.Id("A"), c = F.Id("c"), w = F.Id("w"), b = F.Id("B");
        Formula jVal = Call("val", j), kVal = Call("val", k);
        Formula difference = NatSub(jVal, kVal);
        Formula modes = Call("Mode", m), pairs = Call("Fin", Add(jVal, D(1)));
        Formula jBinder = Typed(j, modes), kBinder = Typed(k, pairs);
        Formula coefficient = new Formula.Fraction(
            Add(D(1), new Formula.Fraction(Mul(RealCast(t), Sub(s, D(1))), D(2))),
            new Formula.Apply(a, [t]));
        Formula weight = Root(Mul(new Formula.Apply(a, [kVal]), new Formula.Apply(a, [difference])));

        Formula wjk = new Formula.Apply(w, [j, k]), wjl = new Formula.Apply(w, [j, l]);
        Formula bjk = new Formula.Apply(b, [j, k]), bjl = new Formula.Apply(b, [j, l]);
        Formula block = Indexed(Sum, k, pairs, Indexed(Sum, l, pairs,
            Call("smul", Mul(wjk, wjl), Mul(new Formula.Power(bjk, Star), bjl))));
        Formula ordered = Indexed(Sum, j, modes,
            Call("smul", new Formula.Fraction(new Formula.Apply(c, [jVal]), D(2)), block));
        Formula upper = Call("Sector", m, n, m), lower = Call("Sector", m, NatSub(n, D(2)), NatSub(m, jVal));
        Formula u = F.Id("u"), v = F.Id("v"), eta = F.Id("eta"), zeta = Zeta, i = F.Id("i");
        Formula matching = Quantify(Equal(Occupation(eta, i),
            Add(Occupation(zeta, i), Add(Indicator(Equal(i, u), Naturals()), Indicator(Equal(i, v), Naturals())))),
            Typed(i, modes));
        Formula count = Mul(RealCast(Occupation(eta, u)),
            Sub(RealCast(Occupation(eta, v)), Indicator(Equal(u, v), Reals())));
        return new Formula.Aligned([
            Seq(Amp, Quantify(Word("let"),
                Typed(s, Reals()), Typed(n, Naturals()), Typed(m, Naturals()))),
            Seq(Amp, Quad, Sp, Assign(a, LambdaOf(Call("raney", s, D(1), t), Typed(t, Naturals()))), Comma),
            Seq(Amp, Quad, Sp, Assign(c, LambdaOf(coefficient, Typed(t, Naturals()))), Comma),
            Seq(Amp, Quad, Sp, Assign(w, LambdaOf(weight, jBinder, kBinder)), Comma),
            Seq(Amp, Quad, Sp, Assign(b, LambdaOf(Word("let"), jBinder, kBinder)), Sp,
                Assign(u, ModeAt(kVal, modes)), Comma, Sp, Assign(v, ModeAt(difference, modes)), Sp, Word("in")),
            Seq(Amp, Qquad, LambdaOf(Word("if"), Typed(zeta, lower), Typed(eta, upper))),
            Seq(Amp, Qquad, Quad, Parenthesized(matching)),
            Seq(Amp, Qquad, Quad, Word("then"), Sp, OfReal(Root(count)), Sp, Word("else"), Sp, D(0), Sp, Word("in")),
            Seq(Amp, Call("hamiltonian", s, n, m), Sp, Eq, Sp,
                Word("if"), Sp, new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, n), Sp, Word("then")),
            Seq(Amp, Quad, ordered),
            Seq(Amp, Word("else"), Sp, D(0))]);
    }

    private static Formula ClaimBody(bool includeClaimName = false)
    {
        Formula sigma = F.Id("s"), n = F.Id("N"), m = F.Id("M");
        Formula h = F.Id("H"), e = F.Id("E"), v = F.Id("v");
        Formula sector = Call("Sector", m, n, m);
        Formula vectorType = new Formula.TypeArrow(sector, Seq(Mathbb, Grp(F.Id("C"))));
        Formula instance = Seq(OpenBracket, Call("Nonempty", sector), CloseBracket);
        Formula premise = new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, sigma);
        Formula binders = Quantify(Seq(Parenthesized(premise), Sp, F.Implies, Sp,
            Quantify(Word("let"), Typed(n, Naturals()), Typed(m, Naturals()), instance)), Typed(sigma, Reals()));
        return new Formula.Aligned([
            includeClaimName ? Seq(F.Id("claim"), Sp, Iff, Amp, Sp, binders) : Seq(Amp, binders),
            Seq(Amp, Quad, Sp, Assign(h, Call("hamiltonian", sigma, n, m)), Comma, Quad, Sp,
                Assign(e, Call("energy", sigma, n, m)), Comma),
            Seq(Amp, Quad, Assign(Typed(v, vectorType), Call("occupationVector", Call("raney", sigma, D(1)))),
                Sp, Word("in")),
            Seq(Amp, Quad, Call("IsHermitian", h), Sp, Land),
            Seq(Amp, Quad, Call("IsGreatest", Call("spectrum", Reals(), h), e), Sp, Land),
            Seq(Amp, Quad, Sp, new Formula.Relation(v, FormulaRelationOperator.NotEqual, D(0)), Sp, Land),
            Seq(Amp, Quad, Equal(Call("mulVec", h, v), Call("smul", e, v)))]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Word(name), [.. arguments]);
    private static Formula Word(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Indexed(Formula op, Formula index, Formula domain, Formula body) =>
        Seq(op, Underscore, Grp(new Formula.Relation(index, FormulaRelationOperator.MemberOf, domain)), Sp, body);
    private static Formula Assign(Formula lhs, Formula rhs) => Seq(lhs, Sp, Colon, Eq, Sp, rhs);
    private static Formula LambdaOf(Formula body, params Formula[] binders) =>
        Seq(LambdaLower, Sp, Seq(binders), Sp, Mapsto, Sp, body);
    private static Formula ModeAt(Formula label, Formula modes) => new Formula.Subscript(Seq(Langle, label, Rangle), modes);
    private static Formula Indicator(Formula condition, Formula type) =>
        new Formula.Subscript(Seq(OpenBracket, condition, CloseBracket), type);
    private static Formula Occupation(Formula state, Formula mode) => new Formula.Apply(Call("val", state), [mode]);
    private static Formula NatSub(Formula x, Formula y) => new Formula.Subscript(Parenthesized(Sub(x, y)), Naturals());
    private static Formula RealCast(Formula value) => new Formula.Apply(new Formula.Subscript(Word("cast"), Reals()), [value]);
    private static Formula OfReal(Formula value) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("Complex"), Dot, F.Id("ofReal"))), [value]);
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Equal(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Quantify(Formula body, params Formula[] binders) =>
        Seq(Forall, Sp, Seq(binders), Comma, Sp, body);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}
