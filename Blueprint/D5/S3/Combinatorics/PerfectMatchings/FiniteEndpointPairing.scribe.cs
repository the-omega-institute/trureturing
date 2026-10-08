using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class FiniteEndpointPairingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite alternating paths pair exposed endpoints and determine all reattached endpoint orbits.",
        H("Finite Alternating Paths and Endpoint Pairing"),
        Blocks(
            Paragraph(Text("Let X be finite and let s and r be involutive permutations of X. "
                + "Put E = {x : r(x)=x} and q=s*r, with the right factor applied first. "
                + "For x in E, take the least positive n with q^n(x) in E. Such n exists by finite "
                + "permutation recurrence. P(s,r)(x) is this actual first-return endpoint. "
                + "A first-return segment has no intermediate point in E. "
                + "For a permutation J of E, extend(J) acts as J on E and fixes X outside E.")),
            Node("endpoint-involution", "First Return Reverses the Same Path", "endpoint_pairing_involutive",
                Context(Call("Involutive", P())),
                "The identity q^n*r*q^n=r reverses any segment with endpoints fixed by r. "
                + "If a reverse segment met E earlier, reversing that shorter segment would contradict "
                + "minimality of the original return time. Thus the two return times agree and P squares to the identity."),
            Node("endpoint-no-fixed", "A Free Corner Matching Gives Distinct Endpoints", "endpoint_pairing_fixed_point_free",
                Context(Imp(Call("FixedPointFree", V("s")),
                    All("x", E(), NotEqual(Call("apply", P(), V("x")), V("x"))))),
                "If a first return ended where it began, an even-length return would give an earlier "
                + "r-fixed midpoint. An odd-length return would give an s-fixed midpoint. "
                + "The first is excluded by minimality and the second by the absence of fixed points of s."),
            Node("reattachment-orbits", "The Constructed Pairing Computes Reattached Orbits", "endpoint_pairing_reattach_same_cycle",
                Context(All("J", Call("Perm", E()), All("x", E(), All("y", E(),
                    Iff(Call("SameCycle", Multiply(V("s"), Multiply(V("r"), Call("extend", V("J")))), V("x"), V("y")),
                        Call("SameCycle", Multiply(P(), V("J")), V("x"), V("y"))))))),
                "Changing the attachment acts only at E. Starting at x, the new walk first attaches "
                + "to J(x), then follows the unchanged interior path to P(J(x)). "
                + "Induction on a finite walk length decomposes every return into these actual segments. "
                + "Conversely, each P*J step is a finite segment of the original permutation, so the two orbit relations agree."))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);
    private static Formula V(string x) => F.Id(x);
    private static Formula E() => Call("Fix", V("r"));
    private static Formula P() => Call("P", V("s"), V("r"));
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Context(Formula body) => Disp(All("X", V("FiniteType"),
        All("s", Call("Perm", V("X")), All("r", Call("Perm", V("X")),
            Imp(And(Call("Involutive", V("s")), Call("Involutive", V("r"))), body)))));
}
