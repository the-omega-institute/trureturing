using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;
internal sealed class ContinuousFiniteImageTailDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Statement() => Disp(All("inputs", V("ProperStageInputs"),
        Imp(Call("OriginalLawsAndDiracReadback", V("inputs")),
            All("f", Call("ContinuousMap", Call("ClosedDomain", V("inputs")), Call("StageSpace", V("inputs"))),
                All("C", Call("Clopens", Call("StageSpace", V("inputs"))),
                    Call("Not", And(Call("AllSourceImagesIn", V("inputs"), V("f"), V("C"), V("false")),
                        Call("AllSourceImagesOutside", V("inputs"), V("f"), V("C"), V("true")))))))));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original proper-stage signed laws forbid continuous clopen separation of the two original source pools.",
        H("Proper-stage continuous preimage obstruction"), Blocks(
            Describe.Lean(DescribeId.Create("proper-f-clopen-dichotomy"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail.proper_F_clopen_dichotomy"),
                H("Original proper F forces finite clopen visits or misses"),
                StatementSource.FromAuthor(Disp(All("inputs", V("ProperOriginalDiracLiftInputs"),
                    Imp(Call("OriginalLawsAndAllNDiracReadback", V("inputs")),
                        All("Dc", Call("Clopens", Call("StageSpace", V("inputs"))),
                            new Formula.Logic(Call("Finite", Call("VisitsAlongOriginalJ", V("inputs"), V("Dc"))),
                                FormulaLogicOperator.Or,
                                Call("Finite", Call("MissesAlongOriginalJ", V("inputs"), V("Dc")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(Paragraph(Text(
                    "ProperOriginalDiracLiftInputs consists exactly of l, H : Prefix l, D : H.Data, its original Laws, r,d,c in Coord l with omega <= r, r < c and d < c, and a whole point sequence z in H.Space(c). "
                    + "For every n the original D.nu(r,d,n) is the signed Dirac at the actual projection H.map(r,c,z(n)). No split, replacement J, pool or final-history premise is present. "
                    + "VisitsAlongOriginalJ is {n in D.J(r,d,c) | z(n) in Dc}; MissesAlongOriginalJ uses the complement. For every actual clopen Dc at that proper stage, one of those two sets is finite. "
                    + "The proof selects the entire Dirac lift, then invokes the original every-selection F law. Testing weak-star convergence at the continuous clopen indicator excludes two infinite sets of opposite values by epsilon one-third. "
                    + "This result is consumed below after original B/C/DJ preserve both source pools across a finite error. It is not final-stage F or an assumed finite-image law."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("no-continuous-pool-separation"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail.no_continuous_pool_separation"),
                H("No continuous separation of a historical J replacement"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(Paragraph(Text(
                    "ProperStageInputs abbreviates precisely the theorem's parameters: an ordinal l, an actual SignedProperLimit.Prefix H l, D : H.Data and its Laws, r,d,b,c in Coord l, omega <= r, r < b, d < b and b <= c. "
                    + "The Bool-indexed pools M are contained in the original reservoirs D.N(r,d,e), and the actual stored D.J(r,d,b) equals their union. A is any closed subset of H.Space(c), and x is a whole Nat-indexed point sequence in A. "
                    + "OriginalLawsAndDiracReadback includes the preceding facts and, for every natural n, the equality of the original D.nu(r,d,n) with the signed Dirac at H.map(r,c,x(n)). It includes all of the existing Laws, with every-selection F; no common measure is chosen before the sequence. "
                    + "The conclusion says that for any continuous f : A -> H.Space(c) and any clopen C, the images f(x(n)) cannot all lie in C on M(false) and all lie outside C on M(true). Neither pool is assumed infinite: their intersections with the later J are proved infinite from the original laws.")),
                    Paragraph(Text(
                    "The continuous set preimage of C is relatively clopen in the closed domain. Compact zero-dimensional separation extends it to an ambient clopen Dc. DJ makes the later J almost contained in the two pools. After deleting its actual finite error, original C and disjoint original reservoirs B give two infinite intersections with this same J. "
                    + "The selected Dirac lifts have norm one and push to the original source sequence for every n, including indices outside the pools. Proper-stage F then provides a weak-star limit. Evaluation at the continuous clopen indicator gives convergence of values which are one and zero on the two infinite pools. Epsilon one-third contradicts that convergence.")),
                    Paragraph(Text(
                    "This is a local obstruction for the continuous finite-image argument on the same signed history. It neither constructs a raw history nor asserts the occurrence of a delayed event. The final application must obtain the actual replacement and whole-fibre clopen from the same executed delayed-successor witness and reflect the ambient preimage to a later proper stage. Full CH construction, the final finite-image endpoint and official acceptance remain open."))), DescribeRole.Theorem))));
}
