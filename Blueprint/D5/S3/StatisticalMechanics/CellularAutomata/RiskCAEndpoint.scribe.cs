using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class RiskCAEndpointDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/ariasnoguerales2026riskca");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A collision in the deterministic RiskCA at the highest active threshold.",
        H("Noninjectivity on complete finite boards"),
        Blocks(
            Paragraph(Text("Use the complete simple graph on V. The carrier S(V,P,M) is the full product over V of P available owner labels and the unit counts 1 through M. Equality is pointwise. The map Φ(π,b,ρ,X) applies the deterministic local step of §3.2 and Appendix B Algorithm 1 to X with priority permutation π, fortification flag b, battle ratio ρ, growth zero and threshold M − 1.")),
            Describe.Lean(
                DescribeId.Create("riskca-highest-active-threshold-fixed-image"),
                DeclarationHandle.Create(Owner + "paper_collision_fixed_image"),
                H("Two configurations map to the same fixed image"),
                StatementSource.FromAuthor(Collision(fixedImage: true)), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Choose distinct vertices u and v. Put M units at u and one unit everywhere else. Assign one owner to v and a different owner everywhere else. The unique request is from u to v. Its committed force is M − 1 and the defending cell has one unit. For ρ ≥ 1 the attack wins and the ceiling of 1/ρ is one, leaving M − 2 units at v.")),
                    Paragraph(Text("The output Y has one owner and one unit everywhere except at v. Its threats vanish and the zero-growth step fixes it. At u the two inputs have M units and one unit, respectively."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("riskca-highest-active-threshold-noninjective"),
                DeclarationHandle.Create(Owner + "paper_noninjective"),
                H("Noninjectivity in the paper's ratio band"),
                StatementSource.FromAuthor(Collision(fixedImage: false)), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For 1 < ρ < 2 the fixed-image collision gives two distinct configurations with equal images. This settles the complete-board branch registered for Proposition 2. The branch for connected incomplete boards with fortification disabled remains open in this formalization."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("arias-noguerales-2026-riskca-complete-board-endpoint"),
                    ResolutionKind.Proved)))));

    private static Formula Collision(bool fixedImage)
    {
        Formula v = F.Id("V"), p = F.Id("P"), m = F.Id("M"), b = F.Id("b");
        Formula x = F.Id("X"), y = F.Id("Y");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = new Formula.Apply(F.Id("S"), [v, p, m]);
        Formula StepAt(Formula state) => new Formula.Apply(Phi, [Pi, b, Rho, state]);
        Formula ratio = fixedImage ? Seq(D(1), Sp, Leq, Rho) : Seq(D(1), Lt, Rho, Lt, D(2));
        Formula outputs = fixedImage
            ? Seq(StepAt(x), Eq, y, Sp, Land, Sp, StepAt(y), Eq, y)
            : Seq(StepAt(x), Eq, StepAt(y));
        return Disp(new Formula.Aligned([
            Seq(Binder(Forall, v, F.Id("Type")), OpenBracket, Call("Fintype", v), CloseBracket,
                Comma, Sp, Binder(Forall, Seq(p, Comma, m), nat),
                Binder(Forall, Pi, Call("Perm", v)), Binder(Forall, b, F.Id("Bool")),
                Binder(Forall, Rho, real)),
            Seq(Open, D(2), Sp, Leq, Sp, Call("card", v), Sp, Land, Sp, D(2), Sp, Leq, Sp, p,
                Sp, Land, Sp, D(3), Sp, Leq, Sp, m, Sp, Land, Sp, ratio, Close, Sp, Longrightarrow),
            Seq(Binder(Exists, Seq(x, Comma, y), space), x, Sp, Neq, Sp, y, Sp, Land, Sp, outputs),
        ]));
    }

    private static Formula Binder(Formula quantifier, Formula variable, Formula type) =>
        Seq(quantifier, Sp, variable, Colon, Sp, type, Comma, Sp);

    private static Formula Call(string function, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(function))), [.. args]);
}
