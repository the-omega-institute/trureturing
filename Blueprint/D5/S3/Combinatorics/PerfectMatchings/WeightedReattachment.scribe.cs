using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class WeightedReattachmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/WeightedReattachment.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual cut paths determine the complete reattached cycle inventory and its independent fair-band law.",
        H("Weighted Reattachment and the Fair-Band Distribution"),
        Blocks(
            Paragraph(Text("Let X be finite and s,r involutive permutations. Put E=Fix(r), q=s*r, "
                + "and P equal to the constructed first-return endpoint pairing. For any permutation J of E, "
                + "reattach by f=s*(r*extend(J)). The length l_J(x) is the actual least positive q-time "
                + "from J(x) to the next exposed endpoint. The reattached return permutation is H=P*J. "
                + "No supplied boundary pairing, classifier transport, orbit size, or cycle partition is assumed. "
                + "The theorem remains valid without fixed-point-freeness; physical ribbon interpretations additionally use a free corner matching.")),
            Describe.Lean(DescribeId.Create("reattachment"),
                DeclarationHandle.Create(Prefix + "reattachment_weighted_cycle_inventory"),
                H("Actual Reattachment Retains Every Cycle and Its Length"),
                StatementSource.FromAuthor(Context(All("J", Call("Perm", Call("Fix", V("r"))),
                    Call("CompleteWeightedReattachment", V("s"), V("r"), V("J"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The statement supplies original cut first-visit witnesses, the full tower successor conjugacy, "
                    + "equality of untouched-cycle sets, equality of every untouched iterate before and after reattachment, "
                    + "and the complete inventory identity. It constructs return data using FiniteEndpointPairing, "
                    + "then consumes the greedy tower and least-period proofs. If L_J(x) is the sum of l_J around the H-cycle, "
                    + "the marked term is sum_x l_J(x) Z^L_J(x)/L_J(x). The unmarked term uses the original q-periods."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the exact conditional signed-ribbon law, let B be any finite set of unresolved bands and "
                + "e:B times Fin(4) -> E a bijection. Every sign state is a function omega:B->Bool, each equally likely. "
                + "On one labelled quadruple the two matchings are J0=(0 2)(1 3) and J1=(0 3)(1 2); "
                + "bandPairs(omega) uses the selected matching independently on each band. Transport it by e to obtain J_omega. "
                + "The remaining attachments and corner matching are held fixed. This models conditioning on rotations and all resolved signs. "
                + "Distinct flags are required by e even when the underlying graph has loops or parallel bands.")),
            Describe.Lean(DescribeId.Create("fair-law"), DeclarationHandle.Create(Prefix + "fair_band_inventory_law"),
                H("The Entire Cycle-Inventory Distribution Under Fair Band Signs"),
                StatementSource.FromAuthor(Context(All("B", V("FiniteType"),
                    All("e", Call("Equiv", Call("Product", V("B"), Call("Fin", Num(4))), Call("Fix", V("r"))),
                        All("test", Call("Function", Call("Polynomial", V("Rational")), V("Rational")),
                            Equal(Call("FairMeanOriginalInventoryTest", V("s"), V("r"), V("e"), V("test")),
                                Call("FairMeanWeightedInventoryTest", V("s"), V("r"), V("e"), V("test")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both sides average test over the 2^card(B) equally weighted Boolean sign states. "
                    + "The arbitrary rational-valued test is applied to the complete inventory polynomial before averaging. "
                    + "Indicator tests therefore recover every inventory probability and every joint cycle-length event, "
                    + "rather than only separate expected cycle counts. The proof is the pointwise constructed inventory identity followed by finite averaging. "
                    + "No claim is made of a polynomial-time evaluation, a new circuit-nullity theorem, unlabelled-map uniformity, "
                    + "or an exact-thirds law. This is reusable formal infrastructure for an explicitly stated labelled sampler."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Context(Formula body) => Disp(All("X", V("FiniteType"),
        All("s", Call("Perm", V("X")), All("r", Call("Perm", V("X")),
            Imp(And(Call("Involutive", V("s")), Call("Involutive", V("r"))), body)))));
}
