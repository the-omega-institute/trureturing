using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class FilteredTwoCocycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native two-cocycle primitives lift through equivariant short exact sequences and finite stable filtrations.",
        H("Lifting two-cocycle primitives"),
        Blocks(
            Describe.Lean(DescribeId.Create("filtered-two-cocycle-exact"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/FilteredTwoCocycle.all_two_cocycles_are_coboundaries_of_short_exact"),
                H("An actual equivariant short exact sequence"),
                StatementSource.FromAuthor(ExactStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The coefficient ring R is any commutative ring, G any group, and A, B and C arbitrary R-modules in independent universes. The maps i and q are native Representation.IntertwiningMap values. Their range and kernel are those of their underlying linear maps. Htwo(rho) abbreviates AllTwoCocyclesAreCoboundaries rho: every native raw groupCohomology.IsCocycle₂ for precisely the action rho has a native IsCoboundary₂ primitive.")),
                    Paragraph(Text("Project a B-valued cocycle f to C and obtain its one-cochain primitive c. Choose a pointwise lift b of c through q. The residual f minus d(b) has values in the kernel of q. Exactness lifts this residual to A; injectivity of i transfers the cocycle identity to that lift. An A-valued primitive a then gives the B-valued primitive b plus i(a). No linear or equivariant section of q is assumed.")),
                    Paragraph(Text("This is a direct cochain construction of the familiar exact-sequence vanishing implication. The construction uses Mathlib's raw low-degree predicates and intertwining maps; no literature novelty is claimed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("filtered-two-cocycle-filtration"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/FilteredTwoCocycle.is_coboundary_two_of_finite_stable_filtration"),
                H("The actual successive quotients suffice"),
                StatementSource.FromAuthor(FiltrationStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In this formula, Coc(rho,f) and Bound(rho,f) are the native raw cocycle and coboundary predicates with SMul g x defined by rho g x. Thus Coc means f(gh,j) plus f(g,h) equals rho(g)f(h,j) plus f(g,hj), and Bound means there exists b with rho(g)b(h) minus b(gh) plus b(g) equal to f(g,h) for every g and h.")),
                    Paragraph(Text("Write Step(F,k) for filtrationStep F k, the inverse image of F k under the native subtype of F(k+1). Grade(F,k) is filtrationGrade F k: the quotient representation of F(k+1) by Step(F,k), on the actual Submodule.Quotient carrier. Monotonicity identifies the range of F k inclusion with Step(F,k), while the kernel of the quotient map is exactly this submodule.")),
                    Paragraph(Text("Induction starts at the zero subrepresentation and applies the equivariant short exact construction at each successive quotient. At F n equal to top, the resulting primitive maps to the original ambient module. The filtration length may be zero. Neither G nor the coefficient module needs to be finite; no dimension, semisimplicity or split-filtration condition is imposed.")),
                    Paragraph(Text("FilteredExtensionSplitting uses this primitive on the actual factor cocycle of a group extension. Separate trace-one operators on the native grades supply the graded hypotheses in its finite-group specialization. The filtration theorem neither assumes nor constructs a trace-one operator on the ambient coefficients."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => Call(name, args);
    private static Formula B(string name, Formula type) => Seq(Open, V(name), Colon, Sp, type, Close);
    private static Formula I(string name, params Formula[] args) => Seq(OpenBracket, C(name, args), CloseBracket, Sp);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, B(name, type), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) => Seq(Grp(premise), Sp, Rightarrow, Sp, body);
    private static Formula Htwo(string rho) => C("Htwo", V(rho));
    private static Formula Representation(string carrier) => C("Representation", V("R"), V("G"), V(carrier));

    private static Formula ExactStatement()
    {
        Formula conclusion = Htwo("b");
        conclusion = Imp(Htwo("c"), conclusion);
        conclusion = Imp(Htwo("a"), conclusion);
        conclusion = Imp(Seq(C("range", V("i")), Eq, C("ker", V("q"))), conclusion);
        conclusion = Imp(C("Surjective", V("q")), conclusion);
        conclusion = Imp(C("Injective", V("i")), conclusion);
        conclusion = All("q", C("IntertwiningMap", V("b"), V("c")), conclusion);
        conclusion = All("i", C("IntertwiningMap", V("a"), V("b")), conclusion);
        conclusion = All("c", Representation("C"), conclusion);
        conclusion = All("b", Representation("B"), conclusion);
        conclusion = All("a", Representation("A"), conclusion);
        return Disp(Seq(Forall, Sp, B("R", V("Type")), Sp, B("G", V("Type")), Sp,
            B("A", V("Type")), Sp, B("B", V("Type")), Sp, B("C", V("Type")), Sp,
            I("CommRing", V("R")), I("Group", V("G")),
            I("AddCommGroup", V("A")), I("Module", V("R"), V("A")),
            I("AddCommGroup", V("B")), I("Module", V("R"), V("B")),
            I("AddCommGroup", V("C")), I("Module", V("R"), V("C")), Comma, Sp, conclusion));
    }

    private static Formula FiltrationStatement()
    {
        Formula grade = All("k", V("Nat"), Imp(Seq(V("k"), Lt, V("n")),
            C("Htwo", C("Grade", V("F"), V("k")))));
        Formula result = All("f", Seq(Open, V("G"), Times, V("G"), Close, To, Sp, V("M")),
            Imp(C("Coc", V("r"), V("f")), C("Bound", V("r"), V("f"))));
        result = Imp(grade, result);
        result = Imp(Seq(C("F", V("n")), Eq, C("top")), result);
        result = Imp(Seq(C("F", D(0)), Eq, C("bot")), result);
        result = All("n", V("Nat"), result);
        result = Imp(C("Monotone", V("F")), result);
        result = All("F", Seq(V("Nat"), To, Sp, C("Subrepresentation", V("r"))), result);
        result = All("r", Representation("M"), result);
        return Disp(Seq(Forall, Sp, B("R", V("Type")), Sp, B("G", V("Type")), Sp,
            B("M", V("Type")), Sp, I("CommRing", V("R")), I("Group", V("G")),
            I("AddCommGroup", V("M")), I("Module", V("R"), V("M")), Comma, Sp, result));
    }
}
