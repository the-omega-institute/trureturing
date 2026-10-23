using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetNumberedHistoriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetNumberedHistories.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [B("q", I("Nat")), B("hq", Call("NatPositive", I("q")))], body);
    private static Formula Matrix => Call("resetMatrix", I("q"));
    private static Formula Paths => Call("ResetPath", I("q"));
    private static Formula Histories => Call("History", Call("expandedGraph", Matrix));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Apply(Formula f, Formula x) => Call("apply", f, x);
    private static Formula At(Formula x, Formula t) => Call("coordinate", x, t);
    private static Formula E(Formula x) => Apply(I("e"), x);
    private static Formula SymmE(Formula y) => Apply(Call("symm", I("e")), y);
    private static Formula CodingLaws => And(
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("x", Paths), B("t", I("Int"))],
            Equal(At(E(I("x")), I("t")),
                Call("numberedStep", I("q"), I("hq"),
                    Call("positiveAdjacentPair", I("x"), I("t"))))),
        And(new Formula.BindMany(FormulaQuantifier.ForAll,
                [B("y", Histories), B("t", I("Int"))],
                Equal(At(SymmE(I("y")), I("t")),
                    Call("pair", Call("toAdd", Call("groupCoordinate", At(I("y"), I("t")))),
                        Call("sourceSuffix", At(I("y"), I("t")))))),
            And(new Formula.BindMany(FormulaQuantifier.ForAll, [B("x", Paths)],
                    Equal(E(Call("resetShift", I("q"), I("x"))),
                        Call("shift", Call("expandedGraph", Matrix), E(I("x"))))),
                new Formula.BindMany(FormulaQuantifier.ForAll, [B("x", Paths)],
                    Equal(E(Call("resetComplement", I("q"), I("x"))),
                        Call("groupHistory", Matrix, Call("ofAdd", I("true")), E(I("x"))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual positive-kernel reset space retains its absolute sign and suffix in a numbered, equivariant topological coding.",
        H("Reset paths as numbered expanded histories"),
        Blocks(
            Describe.Lean(DescribeId.Create("reset-group-matrix"),
                DeclarationHandle.Create(Prefix + "resetMatrix"),
                H("The Boolean group matrix"),
                StatementSource.FromAuthor(Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
                    [B("q", I("Nat")), B("i", Call("Fin", I("q"))), B("j", Call("Fin", I("q")))],
                    Equal(Call("entry", Matrix, I("i"), I("j")),
                        Call("sum", Call("indicatorSingle", Call("isZero", I("j")),
                                Call("ofAdd", I("true")), I("one")),
                            Call("indicatorSingle", Call("isSuccessor", I("i"), I("j")),
                                I("groupIdentity"), I("one"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sign is Multiplicative Bool with the native BooleanRing Bool addition, namely XOR; its identity is ofAdd false and tau is ofAdd true. The natural group matrix C(i,j) is single(tau,1) when j.val=0, plus single(1,1) when j.val=i.val+1. The two target conditions are disjoint. Thus each allowed labelled edge has coefficient one and number in Fin 1. No adjacency with forgotten labels or forgotten parallel-edge numbers replaces this matrix."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("numbered-reset-homeomorphism"),
                DeclarationHandle.Create(Prefix + "resetHomeomorph"),
                H("Local encoding and source decoding"),
                StatementSource.FromAuthor(Disp(All(Call("Homeomorph", Paths, Histories)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("NatPositive(q) means 0<q, with no additional assumption q>=2. ResetPath q is precisely ParryBilateralLaw.ResetPath: an Int-indexed sequence x_t=(b_t,i_t) for which TwistedResetPaths.kernel q (ParryResetLaw.parryParameter q) x_t x_(t+1)>0 at every integer origin. History is the existing subtype of Int-indexed expanded edges whose targets equal the next sources. Both spaces use their native product and subtype topologies, with the native discrete Bool, Fin and Multiplicative coordinate instances.")),
                    Paragraph(Text("For q>=2, parry_stationary_law gives p>1/2 and p<=suffixWeight(q,p,i). Hence reset mass p/h_i and increment mass p*h_j/h_i are strictly positive. For q=1, the defined fallback parameter is 1/2 and the only suffix weight is 1/2, so reset mass is one. Increment is impossible. In either case the actual positive support consists exactly of a sign flip to suffix zero or a sign-preserving suffix increment. The one-suffix calculation is a deterministic flip and makes no claim that the fallback inverse parameter is the spectral radius of the unweighted transition.")),
                    Paragraph(Text("numberedStep maps a positive adjacent pair ((b,i),(d,j)) to the edge with source i, target j, label ofAdd(xor b d), and number zero, together with absolute group coordinate ofAdd b. The support calculation proves that this precise label has coefficient one in C(i,j). The expanded target is (j,ofAdd b * ofAdd(xor b d))=(j,ofAdd d); it equals the next expanded source. The order is the existing right multiplication of the current group coordinate by the edge label.")),
                    Paragraph(Text("The inverse reads (toAdd groupCoordinate,edge.source) at each time. An arbitrary numbered edge supplies a positive coefficient through its Fin number. The coefficient formula forces exactly one of the reset and increment alternatives; the actual history seam then supplies the next suffix and sign. This proves positive kernel support of the decoded path. Decoding an encoded path recovers every original coordinate. Encoding a decoded history recovers the same source, target and label; coefficient one forces its original number to be zero. Thus both inverse identities hold for the actual histories, rather than only for label projections.")),
                    Paragraph(Text("Continuity of encoding is coordinatewise: the output at t is a discrete local function of input coordinates t and t+1. Decoding is a discrete local function of one expanded-edge coordinate t. Evaluation in the product topology and the subtype continuity rules give the homeomorphism. This construction does not use or repeat the private suffix or sign reconstruction in bilateral_reset_coding."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reset-numbered-coding-laws"),
                DeclarationHandle.Create(Prefix + "reset_numbered_coding"),
                H("One construction preserves time and complement"),
                StatementSource.FromAuthor(Disp(All(new Formula.BindMany(FormulaQuantifier.Exists,
                    [B("e", Call("Homeomorph", Paths, Histories))], CodingLaws)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("coordinate means the underlying subtype function evaluated at the given integer. positiveAdjacentPair(x,t) contains (x_t,x_(t+1)) and its actual positive-kernel proof. sourceSuffix and groupCoordinate project the source suffix and absolute group coordinate of that expanded edge. The existential homeomorphism is resetHomeomorph itself, with the forward and inverse coordinates specified above.")),
                    Paragraph(Text("resetShift sends x_t to x_(t+1); on histories shift is FiniteWindowTableCriterion.shift. Both adjacent input coordinates translate by one, so the numbered coding commutes with unit time. resetComplement applies TwistedResetPaths.flip to every source state. Complementing both adjacent signs leaves their XOR label fixed, while the absolute group coordinate changes by left multiplication by tau. Consequently the same coding intertwines complement with FixedBlockRigidity.groupHistory C tau, preserving the suffix, label and edge number.")),
                    Paragraph(Text("The native topological and equivariant identification attaches the positive reset dynamics to the counted group graph. Existing TwistedPeriodicHistories.twistedPeriodEquiv and twistedPeriod_card concern this exact history type, with finite numbered word fibers and ordered signed seams for every positive period. Their generic extension and enumeration need no replacement. This statement does not identify a separate original marked-word language, prove the marked count Fix_K(k,n)+1=Fix_Y(k,n)+k*[k divides n], settle n<q multiple wraparounds, or claim novelty for a published scalar formula. Surviving integral dimension-group classes and an ordered positive cone require their own proofs; no integral splitting of the plus/minus lattices or order-infinitesimal conclusion follows here."))),
                DescribeRole.Theorem))));
}
