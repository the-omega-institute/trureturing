using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class DouglasLemmaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HilbertOperators/DouglasLemma.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/atlas2026douglas");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual range inclusion, bounded factorization and adjoint norm majorization for arbitrary complete real or complex Hilbert spaces, including a factor with every prescribed admissible norm bound.",
        H("Douglas factorization on Hilbert spaces"), Blocks(
            Paragraph(Text("The scalar k is any RCLike field. The carriers E and F are normed additive commutative groups with inner products over k and are complete. Their universe levels v and w and the scalar universe u are independent. Map(k,E,F) means ContinuousLinearMap(k,E,F), a bounded continuous k-linear map. Lin(k,E,E) means an algebraic linear endomorphism. Adjoint(T) is the Hilbert adjoint, Comp(B,C) applies C first and then B, and every map norm is the operator norm.")),
            Paragraph(Text("Range(T) is the actual linear range of T and Kernel(T) its kernel; Orthogonal(U) is the orthogonal complement. The relation Range(A) <= Range(B) is actual submodule inclusion. No closure replaces either range in a conclusion. The scalar c is real and can equal zero. No closed-range, finite-dimensional, separable, injective, surjective or nonzero-space hypothesis is imposed.")),
            Entry("adjoint-norm", "norm_adjoint", Telescope(All("T", Map("E", "F"), Eqn(Norm(Call("Adjoint", V("T"))), Norm(V("T"))))),
                "The adjoint is an isometry on bounded operators. The factorization estimate and the prescribed-bound construction use this norm identity."),
            Entry("orthogonal-preimage-uniqueness", "eq_of_mem_orthogonal_and_apply",
                Telescope(All("B", Map("E", "F"), All("z1", V("E"), All("z2", V("E"),
                    Imp(Member(V("z1"), OrthKernel()), Imp(Member(V("z2"), OrthKernel()),
                        Imp(Eqn(Call("B", V("z1")), Call("B", V("z2"))), Eqn(V("z1"), V("z2"))))))))),
                "Two preimages in the orthogonal complement of the kernel with the same image are equal: their difference belongs both to the kernel and its orthogonal complement, so its squared norm vanishes. This supplies additivity, homogeneity and closed-graph uniqueness for the canonical factor."),
            Entry("orthogonal-preimage-existence", "exists_mem_orthogonal_apply",
                Operators(Imp(Inclusion(), All("x", V("E"), Some("z", V("E"),
                    And(Member(V("z"), OrthKernel()), Eqn(Call("B", V("z")), Call("A", V("x")))))))),
                "For every x, actual range inclusion supplies a preimage of A x. Projecting it onto the orthogonal complement of the kernel preserves its B-image and produces the required orthogonal preimage."),
            Entry("canonical-preimage-function", "douglasFactorFun",
                Operators(All("h", Inclusion(), All("x", V("E"), Eqn(Factor("douglasFactorFun", true),
                    Call("ChooseOrthogonalPreimage", V("B"), Call("A", V("x"))))))),
                "douglasFactorFun(A,B,h,x) is Classical.choose applied to exists_mem_orthogonal_apply(A,B,h,x). ChooseOrthogonalPreimage denotes that choice of a vector z in Orthogonal(Kernel(B)) with B z = A x; existence follows from h and uniqueness follows from eq_of_mem_orthogonal_and_apply. This is a noncomputable choice definition.", DescribeRole.Definition),
            Entry("canonical-preimage-specification", "douglasFactorFun_spec",
                Operators(All("h", Inclusion(), All("x", V("E"), And(Member(Factor("douglasFactorFun", true), OrthKernel()),
                    Eqn(Call("B", Factor("douglasFactorFun", true)), Call("A", V("x"))))))),
                "The chosen preimage lies in the kernel's orthogonal complement and maps under B to A x. Both conjuncts are used to establish the linear and continuous structure."),
            Entry("canonical-linear-factor", "douglasFactorLin",
                Operators(All("h", Inclusion(), All("x", V("E"),
                    Eqn(Factor("douglasFactorLin", true), Factor("douglasFactorFun", true))))),
                "douglasFactorLin packages the chosen preimage function as a k-linear endomorphism. Addition and scalar multiplication preserve orthogonal membership and the required B-image; uniqueness proves the two linearity laws. The formula identifies its underlying function; its bundled type is Lin(k,E,E).", DescribeRole.Definition),
            Entry("closed-graph-continuity", "continuous_douglasFactorLin",
                Operators(All("h", Inclusion(), Call("Continuous", Factor("douglasFactorLin")))),
                "The canonical linear factor is continuous by the sequential closed graph theorem. If x_n tends to x and its images tend to z, closedness of the orthogonal complement keeps z there. Continuity of A and B and uniqueness of limits give B z = A x. Orthogonal-preimage uniqueness identifies z with the canonical image of x, closing the graph."),
            Entry("canonical-bounded-factor", "douglasFactor",
                Operators(All("h", Inclusion(), All("x", V("E"),
                    Eqn(Factor("douglasFactor", true), Factor("douglasFactorLin", true))))),
                "douglasFactor is the continuous linear map whose toLinearMap is douglasFactorLin and whose continuity proof is continuous_douglasFactorLin. Thus the canonical orthogonal-preimage construction is a bounded endomorphism E to E.", DescribeRole.Definition),
            Entry("canonical-factor-applied", "apply_douglasFactor",
                Operators(All("h", Inclusion(), All("x", V("E"), Eqn(Call("B", Factor("douglasFactor", true)), Call("A", V("x")))))),
                "For each x, applying B to the bounded canonical factor recovers A x."),
            Entry("canonical-factorization", "eq_comp_douglasFactor",
                Operators(All("h", Inclusion(), Eqn(V("A"), Call("Comp", V("B"), Factor("douglasFactor"))))),
                "Extensionality turns the pointwise preimage identity into equality of bounded operators."),
            Entry("range-factorization-equivalence", "range_le_iff_exists_factorization",
                Operators(IffOf(Inclusion(), Factorization())),
                "Actual range inclusion is equivalent to existence of a bounded C from E to E with A = B composed with C. The forward direction uses the continuous canonical factor; the converse uses inclusion of the range of a composition in the range of its outer map."),
            Entry("factorization-majorization", "majorization_of_factorization",
                Operators(All("C", Map("E", "E"), Imp(FactorEquation(), All("y", V("F"), Bound(Norm(V("C"))))))),
                "Any bounded factor C gives the pointwise adjoint estimate with constant norm(C). Adjoint composition reverses the order, the operator-norm bound controls C adjoint, and norm_adjoint replaces its norm by norm(C)."),
            Entry("prescribed-bound-factor", "exists_factorization_of_majorization",
                Operators(All("c", Real, Imp(Le(D(0), V("c")), Imp(Majorization(V("c")),
                    Some("C", Map("E", "E"), And(FactorEquation(), Le(Norm(V("C")), V("c")))))))),
                "For every real c >= 0 satisfying the pointwise adjoint bound, a single bounded C realizes both A = B composed with C and norm(C) <= c. Set S to the closure of Range(Adjoint(B)). Restrict Adjoint(B) to the codomain S, obtaining a dense-range linear map e. The estimate allows Adjoint(B)y mapped to Adjoint(A)y to extend to a bounded D from S to E with norm(D) <= c. The factor is the adjoint of D composed with the orthogonal projection from E onto S. Extension equality, projection on S and adjoint composition give the factorization. The projection norm is at most one and adjoints preserve norm, giving the same prescribed bound. Closure is used only for this complete extension domain."),
            Entry("majorization-factorization-equivalence", "majorization_iff_exists_factorization",
                Operators(IffOf(SomeMajorization(), Factorization())),
                "Existence of a nonnegative real majorization constant is equivalent to bounded factorization. One direction uses the prescribed-bound construction. The other uses norm(C), which is nonnegative. This equivalence retains factor existence; the separate prescribed-bound theorem states the quantitative conclusion for each given c."),
            Entry("range-majorization-equivalence", "range_le_iff_majorization",
                Operators(IffOf(Inclusion(), SomeMajorization())),
                "Combining the two factorization equivalences identifies actual range inclusion with existence of a nonnegative real c satisfying the adjoint inequality for every y in F."),
            Paragraph(Text("These statements cover zero operators and zero-dimensional, infinite-dimensional and nonseparable spaces. They assert neither an optimal-constant attainment formula nor a factorization with three distinct source and target domains, naturality, or a Hilbert C*-module analogue. The construction supplies an existence theorem, without a numerical algorithm or an empirical quantum claim.")),
            Paragraph(Text("The actual Lean supplier is the immutable facebookresearch/atlas-lean DouglasLemma source identified in the literature note. The result is classical Douglas factorization. The readable expositions by Manuilov, Moslehian and Xu and by Nayak give same-space classical statements; the arbitrary two-space RCLike formulation here is attested by the cited Lean source. The source and license attribution are recorded in that note and the Lean header.")))));

    private static DocumentBlock Entry(string id, string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Sp, Leq, Sp, y);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Member(Formula x, Formula y) => Seq(x, Sp, InMacro, Sp, y);
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Rightarrow, Sp, y);
    private static Formula And(Formula x, Formula y) => Seq(Par(x), Sp, Land, Sp, Par(y));
    private static Formula IffOf(Formula x, Formula y) => Seq(Par(x), Sp, Iff, Sp, Par(y));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Map(string source, string target) => Call("Map", V("k"), V(source), V(target));
    private static Formula Inclusion() => Le(Call("Range", V("A")), Call("Range", V("B")));
    private static Formula OrthKernel() => Call("Orthogonal", Call("Kernel", V("B")));
    private static Formula Factor(string name, bool apply = false) => apply
        ? Call(name, V("A"), V("B"), V("h"), V("x")) : Call(name, V("A"), V("B"), V("h"));
    private static Formula FactorEquation() => Eqn(V("A"), Call("Comp", V("B"), V("C")));
    private static Formula Factorization() => Some("C", Map("E", "E"), FactorEquation());
    private static Formula Bound(Formula c) => Le(Norm(Call("Apply", Call("Adjoint", V("A")), V("y"))),
        Seq(c, Sp, Cdot, Sp, Norm(Call("Apply", Call("Adjoint", V("B")), V("y")))));
    private static Formula Majorization(Formula c) => All("y", V("F"), Bound(c));
    private static Formula SomeMajorization() => Some("c", Real, And(Le(D(0), V("c")), Majorization(V("c"))));
    private static Formula Operators(Formula body) => Telescope(All("A", Map("E", "F"), All("B", Map("E", "F"), body)));
    private static Formula Telescope(Formula body)
    {
        body = Seq(Inst(Call("RCLike", V("k"))), Inst(Call("NormedAddCommGroup", V("E"))),
            Inst(Call("NormedAddCommGroup", V("F"))), Inst(Call("InnerProductSpace", V("k"), V("E"))),
            Inst(Call("InnerProductSpace", V("k"), V("F"))), Inst(Call("CompleteSpace", V("E"))),
            Inst(Call("CompleteSpace", V("F"))), body);
        Formula TypeAt(string level) => Seq(Operatorname, Grp(V("Type")), Underscore, Grp(V(level)));
        return All("u", Call("UniverseLevel"), All("v", Call("UniverseLevel"), All("w", Call("UniverseLevel"),
            All("k", TypeAt("u"), All("E", TypeAt("v"), All("F", TypeAt("w"), body))))));
    }
}
