using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class FilteredExtensionSplittingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/conrad2012groupextensions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit trace contraction and native graded primitives construct homomorphic sections of abelian-kernel group extensions.",
        H("Splitting from native two-cocycle primitives"),
        Blocks(
            Describe.Lean(DescribeId.Create("filtered-extension-trace-contraction"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.trace_one_primitive_spec"),
                H("An explicit trace-one contraction"),
                StatementSource.FromAuthor(TraceStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("R is any commutative ring, V any R-module, and G any finite group. These carriers have independent universes. Coc(rho,f) is the native raw IsCocycle₂ predicate for the SMul action rho. The abbreviation Trace(rho,t) means the sum over x in G of rho(x) composed with t composed with rho(x inverse). Here b(rho,t,f,g) is traceOnePrimitive rho t f g: the sum over x in G of rho(x) applied to t(f(x inverse,g)).")),
                    Paragraph(Text("Apply rho(x) composed with t to the cocycle equation at (x inverse,g,h), and sum over x. Reindex the term involving x inverse times g by left multiplication by g. The trace-one identity evaluates the remaining conjugate sum to f(g,h). This gives exactly f equal to d(b). The native IsCoboundary₂ predicate uses d(b) equal to f, so all_two_cocycles_are_coboundaries_of_trace_one uses the symmetric equality.")),
                    Paragraph(Text("No commutativity of G, dimension bound, field, inverse group order or projective-module assumption enters the contraction. The operator t itself is the hypothesis. This explicit cochain argument is a classical trace contraction; the stated generality and native interfaces are proved here, with no literature novelty claim."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("filtered-extension-higher-cocycle-section"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.extension_splitting_of_all_two_cocycles_are_coboundaries"),
                H("Correcting the actual extension factor set"),
                StatementSource.FromAuthor(ExtensionStatement(0)), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("U is an arbitrary commutative group and E and G are arbitrary groups in independent universes. S is the given native GroupExtension U E G; i and p denote S.inl and S.rightHom. The prescribed action phi is a homomorphism from G to MulAut U. Compatibility means i(phi(p(e))(u)) equals e i(u) e inverse for every e and u. The integral representation rho(phi) is phiRepresentation phi on Additive U; its value at g,u is Additive.ofMul(phi(g)(Additive.toMul u)).")),
                    Paragraph(Text("Htwo(rho) means every native raw two-cocycle for precisely rho has a native raw primitive. Choose a set-theoretic native Section sigma. Its actual factor c is characterized by i(c(g,h)) equal to sigma(g) sigma(h) sigma(gh) inverse. Associativity and compatibility give c(g,h)c(gh,k) equal to phi(g)(c(h,k))c(g,hk). Commutativity of U converts this to the native additive cocycle equation, without any normalization assumption on sigma.")),
                    Paragraph(Text("For its primitive b, put beta(g) equal to Additive.toMul(b(g)). The native coboundary equation says c(g,h) equals phi(g)(beta(h)) beta(gh) inverse beta(g). Thus delta(g) equal to beta(g) inverse satisfies delta(g) phi(g)(delta(h)) c(g,h) equal to delta(gh). Consequently s(g) equal to i(delta(g)) sigma(g) is a group homomorphism and p(s(g)) equals g. This constructs an actual native S.Splitting. The generic theorem states Nonempty because Splitting is a structure in Type; the definitions below choose an actual structure.")),
                    Paragraph(Text("The extension-to-factor-set correspondence and coboundary correction are classical. Conrad's Group cohomology and group extensions, section 2, gives the factor-set construction and identifies the zero class with the semidirect product. The construction here retains the prescribed action and independent carrier universes. It assumes neither a homomorphic section nor a stronger auxiliary structure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("filtered-extension-native-filtration"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.extension_splitting_of_finite_stable_filtration"),
                H("A finite stable filtration gives an actual section"),
                StatementSource.FromAuthor(ExtensionStatement(1)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The extension and compatibility conventions are those above. F is a monotone sequence of native Subrepresentation values for rho(phi), from bottom at zero to top at n. Grade(F,k) is filtrationGrade F k from FilteredTwoCocycle, on the actual quotient of F(k+1) by the inverse image of F k under its subtype. Htwo is required separately on every such grade with k less than n.")),
                    Paragraph(Text("For each actual ambient cocycle, is_coboundary_two_of_finite_stable_filtration supplies its primitive. Passing this fact to the shared factor correction yields the displayed native Splitting structure. Only the filtration length is finite: G, E and U may be infinite, and n may be zero. No splitting of the coefficient filtration is supplied or required."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("filtered-extension-native-graded-traces"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/FilteredExtensionSplitting.extension_splitting_of_finite_stable_filtration_grade_trace_one"),
                H("Independent trace-one witnesses on the native grades"),
                StatementSource.FromAuthor(ExtensionStatement(2)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here G is finite. Carrier(F,k) denotes the actual underlying quotient module of Grade(F,k). Trace on each grade uses that grade's inherited representation. For every k less than n the hypothesis supplies its own integral linear endomorphism t; the witnesses need not come from one endomorphism of Additive U.")),
                    Paragraph(Text("Apply the explicit trace contraction to each chosen grade witness, obtaining that grade's native Htwo property. The finite-filtration primitive theorem then supplies an ambient primitive, and the shared extension correction gives the actual homomorphic section. The conclusion does not infer a global trace-one operator. There is no logarithm on U or extra field-module structure on the multiplicative kernel.")),
                    Paragraph(Text("The companion extension_splitting_of_trace_one uses a single trace-one integral endomorphism of Additive U directly in the same correction theorem. These constructions assemble classical cochain mechanisms on the given native extension and native quotient carriers. No assertion about a specific principal-unit filtration, semilinear realization, or literature novelty is made."))), DescribeRole.Definition))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => Call(name, args);
    private static Formula B(string name, Formula type) => Seq(Open, V(name), Colon, Sp, type, Close);
    private static Formula I(string name, params Formula[] args) => Seq(OpenBracket, C(name, args), CloseBracket, Sp);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, B(name, type), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) => Seq(Grp(premise), Sp, Rightarrow, Sp, body);
    private static Formula Inv(Formula value) => Seq(Grp(value), Caret, Grp(Minus, D(1)));

    private static Formula TraceStatement()
    {
        Formula r = V("rho"), t = V("t"), f = V("f"), g = V("g"), h = V("h");
        Formula b(Formula x) => C("b", r, t, f, x);
        Formula identity = Seq(C("f", g, h), Eq, C("rho", g, b(h)), Minus,
            b(Seq(g, Cdot, Sp, h)), Plus, b(g));
        Formula body = All("g", V("G"), All("h", V("G"), identity));
        body = Imp(C("Coc", r, f), body);
        body = All("f", Seq(Open, V("G"), Times, V("G"), Close, To, Sp, V("V")), body);
        body = Imp(Seq(C("Trace", r, t), Eq, D(1)), body);
        body = All("t", C("End", V("R"), V("V")), body);
        body = All("rho", C("Representation", V("R"), V("G"), V("V")), body);
        return Disp(Seq(Forall, Sp, B("R", V("Type")), Sp, B("V", V("Type")), Sp,
            B("G", V("Type")), Sp, I("CommRing", V("R")), I("AddCommGroup", V("V")),
            I("Module", V("R"), V("V")), I("Group", V("G")), I("Fintype", V("G")),
            Comma, Sp, body));
    }

    private static Formula ExtensionStatement(int mode)
    {
        Formula phi = V("phi"), s = V("S"), rho = C("rho", phi), f = V("F"), k = V("k"), n = V("n");
        Formula body = C("Splitting", s);
        if (mode == 0)
            body = Imp(C("Htwo", rho), C("Nonempty", body));
        else
        {
            Formula grade = C("Grade", f, k);
            Formula local = C("Htwo", grade);
            if (mode == 2)
                local = Seq(Exists, Sp, B("t", C("End", C("Integers"), C("Carrier", f, k))),
                    Comma, Sp, C("Trace", grade, V("t")), Eq, D(1));
            body = Imp(All("k", V("Nat"), Imp(Seq(k, Lt, n), local)), body);
            body = Imp(Seq(C("F", n), Eq, C("top")), body);
            body = Imp(Seq(C("F", D(0)), Eq, C("bot")), body);
            body = All("n", V("Nat"), body);
            body = Imp(C("Monotone", f), body);
            body = All("F", Seq(V("Nat"), To, Sp, C("Subrepresentation", rho)), body);
        }
        Formula compatibility = All("e", V("E"), All("u", V("U"),
            Seq(C("i", C("phi", C("p", V("e")), V("u"))), Eq,
                V("e"), Cdot, Sp, C("i", V("u")), Cdot, Sp, Inv(V("e")))));
        body = Imp(compatibility, body);
        body = All("phi", C("MonoidHom", V("G"), C("MulAut", V("U"))), body);
        body = All("S", C("GroupExtension", V("U"), V("E"), V("G")), body);
        Formula finite = mode == 2 ? I("Fintype", V("G")) : Sp;
        return Disp(Seq(Forall, Sp, B("U", V("Type")), Sp, B("E", V("Type")), Sp,
            B("G", V("Type")), Sp, I("CommGroup", V("U")), I("Group", V("E")),
            I("Group", V("G")), finite, Comma, Sp, body));
    }
}
