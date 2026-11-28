using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FockSpace;

internal sealed class EvninQuantumSectorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/FockSpace/EvninQuantumSector";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/evnin2026quantumestimates");

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
                + "The Hamiltonian and its eigenvector use r = 1. The convolution in the proof also uses r = 2."),
            Definition("energy", "energy", "Energy of the attaining state", EnergyBody(),
                "Both N and M are cast from natural numbers to real numbers before the arithmetic of Eq. (33)."),
            Definition("vector", "occupationVector", "Factorial occupation vector", VectorBody(),
                "For real mode weights A, each coordinate is computed in the reals and cast to the complex "
                + "numbers. In the theorem, A(i) is raney(s, 1, i) and the vector is indexed by Sector(M, N, M)."),
            Definition("hamiltonian", "hamiltonian", "Normally ordered Hamiltonian", HamiltonianBody(),
                "For N at least two, B with indices j and k is the ordered annihilator for modes k and j − k. "
                + "Its columns are indexed by Sector(M, N, M), and its rows by Sector(M, N − 2, M − j). "
                + "The entry at row ζ and column η vanishes unless η is obtained by adding both particles to ζ. "
                + "In that case the entry is the real square root of η(k) times η(j − k) for distinct modes, "
                + "with the entire product under the root. For equal modes the radicand is η(k)(η(k) − 1). "
                + "Both orders of a distinct-mode pair occur in the ordered sums from Eqs. (19) and (30)."),
            Describe.Lean(
                DescribeId.Create("evnin-quantum-sector-claim"), DeclarationHandle.Create(Module + ".claim"),
                H("Proposition on the top spectral value"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(
                    F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write s for σ. The assertion ranges over nonempty sectors, including the one-particle "
                        + "sectors and the vacuum of zero momentum. The displayed occupation vector uses "
                        + "the implicit sector indices (M, N, M). Greatest means that the energy belongs to "
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
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, Formula body, string explanation) => Describe.Lean(
            DescribeId.Create("evnin-quantum-sector-" + id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(body)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static Formula SectorInstance(string declaration, string type)
    {
        Formula cutoff = F.Id("L"), particles = F.Id("N"), momentum = F.Id("M");
        return Seq(Call(declaration, cutoff, particles, momentum), Sp, Colon, Sp,
            Call(type, Call("Sector", cutoff, particles, momentum)));
    }

    private static Formula ModeBody()
    {
        Formula cutoff = F.Id("L");
        return Equal(Call("Mode", cutoff), Call("Fin", Add(cutoff, D(1))));
    }

    private static Formula SectorBody()
    {
        Formula cutoff = F.Id("L"), particles = F.Id("N"), momentum = F.Id("M");
        Formula eta = F.Id("eta"), mode = F.Id("i"), modes = Call("Mode", cutoff);
        Formula occupation = new Formula.Apply(eta, [mode]);
        Formula domain = new Formula.TypeArrow(modes, Naturals());
        Formula count = Equal(Indexed(Sum, mode, modes, occupation), particles);
        Formula weight = Equal(Indexed(Sum, mode, modes, Mul(mode, occupation)), momentum);
        return Equal(Call("Sector", cutoff, particles, momentum),
            Seq(OpenBrace, eta, Colon, Sp, domain, Sp, Bar, Sp, And(count, weight), CloseBrace));
    }

    private static Formula RaneyBody()
    {
        Formula s = F.Id("s"), r = F.Id("r"), j = F.Id("j");
        Formula numerator = Mul(r, new Formula.Apply(Gamma, [Add(Mul(s, j), r)]));
        Formula first = new Formula.Apply(Gamma, [Add(Add(Mul(Sub(s, D(1)), j), r), D(1))]);
        Formula second = new Formula.Apply(Gamma, [Add(j, D(1))]);
        return Equal(Call("raney", s, r, j), new Formula.Fraction(numerator, Mul(first, second)));
    }

    private static Formula EnergyBody()
    {
        Formula s = F.Id("s"), n = F.Id("N"), m = F.Id("M");
        Formula particles = Typed(n, Reals()), momentum = Typed(m, Reals());
        return Equal(Call("energy", s, n, m), new Formula.Fraction(
            Mul(Sub(particles, D(1)), Add(particles, Mul(Mul(D(2), s), momentum))), D(2)));
    }

    private static Formula VectorBody()
    {
        Formula a = F.Id("A"), i = F.Id("i"), eta = F.Id("eta");
        Formula occupation = new Formula.Apply(eta, [i]);
        Formula weight = new Formula.Apply(a, [i]);
        Formula factorial = Seq(Parenthesized(occupation), Bang);
        Formula amplitude = new Formula.Fraction(new Formula.Power(Root(weight), occupation), Root(factorial));
        Formula product = Indexed(Prod, i, Call("Mode", F.Id("L")), amplitude);
        return Equal(Call("occupationVector", a, eta), Typed(product, Seq(Mathbb, Grp(F.Id("C")))));
    }

    private static Formula HamiltonianBody()
    {
        Formula s = F.Id("s"), n = F.Id("N"), m = F.Id("M");
        Formula j = F.Id("j"), k = F.Id("k"), l = F.Id("l");
        Formula a = F.Id("A"), c = F.Id("c"), w = F.Id("w"), b = F.Id("B");
        Formula aj = new Formula.Subscript(a, j), cj = new Formula.Subscript(c, j);
        Formula wjk = new Formula.Subscript(w, Seq(j, Comma, k));
        Formula wjl = new Formula.Subscript(w, Seq(j, Comma, l));
        Formula bjk = new Formula.Subscript(b, Seq(j, Comma, k));
        Formula bjl = new Formula.Subscript(b, Seq(j, Comma, l));
        Formula adjoint = new Formula.Power(bjk, Star);
        Formula pairs = Call("Fin", Add(j, D(1)));
        Formula block = Indexed(Sum, k, pairs, Indexed(Sum, l, pairs, Mul(Mul(wjk, wjl), Mul(adjoint, bjl))));
        Formula ordered = Indexed(Sum, j, Call("Mode", m), Mul(new Formula.Fraction(cj, D(2)), block));
        Formula h = Call("hamiltonian", s, n, m);
        return new Formula.Aligned([
            Seq(Equal(aj, Call("raney", s, D(1), j)), Comma, Quad, Sp,
                Equal(cj, new Formula.Fraction(Add(D(1), new Formula.Fraction(Mul(j, Sub(s, D(1))), D(2))), aj))),
            Equal(wjk, Root(Mul(new Formula.Subscript(a, k), new Formula.Subscript(a, Sub(j, k))))),
            Seq(Equal(h, ordered), Quad, If(new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, n))),
            Seq(Equal(h, D(0)), Quad, If(new Formula.Relation(n, FormulaRelationOperator.LessThan, D(2))))]);
    }

    private static Formula ClaimBody()
    {
        Formula sigma = F.Id("s"), n = F.Id("N"), m = F.Id("M");
        Formula sector = Call("Sector", m, n, m);
        Formula h = Call("hamiltonian", sigma, n, m);
        Formula vector = Call("occupationVector", Call("raney", sigma, D(1)));
        Formula energy = Call("energy", sigma, n, m);
        Formula conclusion = And(Call("IsHermitian", h), And(
            Call("IsGreatest", Call("spectrum", Reals(), h), energy),
            And(new Formula.Relation(vector, FormulaRelationOperator.NotEqual, D(0)),
                new Formula.Relation(Call("mulVec", h, vector), FormulaRelationOperator.Equal,
                    Call("smul", energy, vector)))));
        return All("s", Reals(), Implies(
            new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, sigma),
            All("N", Naturals(), All("M", Naturals(), Implies(Call("Nonempty", sector), conclusion)))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Indexed(Formula op, Formula index, Formula domain, Formula body) =>
        Seq(op, Underscore, Grp(new Formula.Relation(index, FormulaRelationOperator.MemberOf, domain)), Sp, body);
    private static Formula If(Formula test) => Seq(Operatorname, Grp(F.Id("if")), Sp, test);
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Equal(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}
