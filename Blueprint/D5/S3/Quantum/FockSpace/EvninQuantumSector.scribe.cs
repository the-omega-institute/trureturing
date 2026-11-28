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
            Describe.Lean(
                DescribeId.Create("evnin-quantum-sector-claim"), DeclarationHandle.Create(Module + ".claim"),
                H("The weighted sector and its spectral value"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(
                    F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write s for σ. The sector is indexed by natural occupations η on modes 0 through M with sum N "
                        + "and momentum sum M. Each coordinate is in the normalized bosonic basis of Eq. (22). "
                        + "For N at least two, the ordered annihilator for modes k and j − k maps into "
                        + "particle number N − 2 and momentum M − j on the same mode list. Its matrix entry "
                        + "is zero unless the column is obtained by adding the two particles to the row. "
                        + "The entry is then the square root of the product of their occupations in distinct "
                        + "modes, or the square root of ηₖ(ηₖ − 1) in the repeated mode.")),
                    Paragraph(Text(
                        "Write Aⱼ for the Eq. (31) Gamma quotient at r = 1, cⱼ for "
                        + "(1 + j(σ − 1)/2)/Aⱼ, and wⱼₖ for √(AₖAⱼ₋ₖ). The matrix H is the ordered "
                        + "sum from Eqs. (19) and (30), with both pair indices running from 0 to j, "
                        + "and with coefficient cⱼwⱼₖwⱼₗ/2 on the product of the kth pair adjoint and "
                        + "the lth pair. A pair of momentum above M cannot be removed. For N below two H is zero. "
                        + "The vector v has coordinate given by the product over all modes i of "
                        + "√Aᵢ to the power ηᵢ divided by √(ηᵢ!). The numbers N and M in the energy are real casts. "
                        + "The assertion ranges over nonempty sectors, including the one-particle sector and "
                        + "the vacuum of zero momentum."))),
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

    private static Formula ClaimBody()
    {
        Formula sigma = F.Id("s"), n = F.Id("N"), m = F.Id("M");
        Formula sector = Call("Sector", m, n, m);
        Formula h = Call("hamiltonian", sigma, n, m);
        Formula vector = Call("occupationVector", Call("raney", sigma, D(1)));
        Formula energy = new Formula.Fraction(Mul(Parenthesized(Sub(Typed(n, Reals()), D(1))),
            Parenthesized(Add(Typed(n, Reals()), Mul(Mul(D(2), sigma), Typed(m, Reals()))))), D(2));
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
