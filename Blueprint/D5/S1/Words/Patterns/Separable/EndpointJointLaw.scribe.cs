using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class EndpointJointLawDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Words/Patterns/Separable/EndpointJointLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual marked-cycle law gives the coupled distribution of low-value suffix removals and the terminal endpoint type.",
        H("Coupled endpoint count and terminal type"),
        Blocks(
            Paragraph(Text(
                "A marked cycle retains its initial direct or skew sign, all actual removed permutation shapes, and its actual terminal indecomposable shape. Its probability mass function is the normalized actual shape law from the finite-prefix limit model. The two observations below are taken from the same cycle; they are not sampled independently.")),
            Definition("lowRemovalCount", "Low-value suffix removals",
                "For an actual UnboundedCycle, a terminal node has count zero. A discard node adds one exactly when its current sign is true, and then continues on the tail whose sign is reversed. True denotes a skew cut: its removed right block has lower values than the retained left block. False denotes a direct cut and contributes zero to this count. Thus N counts low-value right suffix removals, not all discard steps."),
            Definition("finiteTerminal", "The terminal endpoint type",
                "At a terminal node with sign s, finiteTerminal is the Boolean negation of s; a discard node passes on the terminal type of its tail. A direct terminal cut therefore gives true. This is the finite-value emission convention of the endpoint-history word in the limit model. Both direct and skew terminal shapes are finite combinatorial objects; the Boolean distinguishes their endpoint emission types, not whether a Lean shape itself is infinite."),
            Definition("observation", "The joint observation",
                "For a marked cycle c, observation(c) is the ordered pair (lowRemovalCount(c),finiteTerminal(c)). Write this pair as (N,chi), with chi=true represented by 1 and chi=false by 0 in probability notation."),
            Definition("endpointPMF", "Pushforward of the actual cycle law",
                "endpointPMF is cyclePMF.map(observation), a probability mass function on natural numbers times Bool. In particular its value at (r,s) is the total actual marked-cycle mass of precisely the cycles with joint observation (r,s). It is not an independently chosen primitive distribution."),
            Paragraph(Text(
                "Put t=sqrt(2)-1 and a=1-1/sqrt(2), as real numbers. The critical shape-law parameter b equals t, and its terminal-shape mass ceiling equals a; the separately named parameter a in the shape-count construction is twice this terminal mass. In the displayed formula p(r,s) abbreviates endpointPMF((r,s)), and ofReal maps a real number to the extended nonnegative reals.")),
            Describe.Lean(DescribeId.Create("actual-endpoint-joint-law"),
                DeclarationHandle.Create(Owner + "whole_endpoint_joint_law"),
                H("The complete coupled endpoint law"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The natural parameter r is unrestricted. The first two equations give the two exceptional masses at zero. The implication gives both masses at every positive r; its exponent 2r-2 is natural-number subtraction, which is ordinary subtraction under r at least one. Consequently u(r)=p(r,true) and v(r)=p(r,false) satisfy u(0)=a, v(0)=a(1+t), u(r)=a*t*(1+t)*t^(2r-2), and v(r)=t*u(r) for all positive r.")),
                    Paragraph(Text(
                        "Enumerate a cycle by its initial sign s and its total number k of discard steps, retaining every actual shape. Structural recursion on the alternating cycle identifies all observation fibers. The observation (0,true) occurs exactly for (s,k)=(false,0). For every natural j, (j+1,true) occurs exactly for (true,2j+1) or (false,2j+2), while (j,false) occurs exactly for (true,2j) or (false,2j+1). These are complete classifications of the actual observations, including zero removals.")),
                    Paragraph(Text(
                        "The total actual shape mass at fixed s,k is ofReal(a*t^k). Reindexing the pushforward sum by the size-preserving cycle enumeration and the classified fibers therefore leaves one term for (0,true) and two terms for every other fiber above. Adding these masses and simplifying yields the four equations. No independence between the count and the terminal type is used.")),
                    Paragraph(Text(
                        "This law concerns the endpoint observations of the existing actual finite-prefix limit model. It does not assert convergence of the entire finite-size endpoint event after an infinite aggregation, nor a reconstructed infinite permutation, a predictable conditional hazard, an occupied-mass lower bound, or discrepancy marginal estimates."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("endpoint-joint-definition-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Apply(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Both(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Mass(Formula r, string terminal) => Apply("p", r, V(terminal));
    private static Formula Lift(Formula x) => Apply("ofReal", x);

    private static Formula Statement()
    {
        var r = V("r");
        var t = V("t");
        var a = V("a");
        var u = Mul(Mul(Mul(a, t), Add(D(1), t)),
            new Formula.Power(t, Sub(Mul(D(2), r), D(2))));
        var positive = new Formula.Logic(
            new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, r),
            FormulaLogicOperator.Implies,
            Both(Eqn(Mass(r, "true"), Lift(u)), Eqn(Mass(r, "false"), Lift(Mul(t, u)))));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("r"),
            Seq(Mathbb, Grp(V("N"))),
            Both(Eqn(Mass(D(0), "true"), Lift(a)),
                Both(Eqn(Mass(D(0), "false"), Lift(Mul(a, Add(D(1), t)))), positive)));
    }
}
