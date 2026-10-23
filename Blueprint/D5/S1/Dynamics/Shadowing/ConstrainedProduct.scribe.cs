using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ConstrainedProductDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/ConstrainedProduct.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Map(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula All(string x, Formula t) => Seq(Forall, Sp, V(x), Colon, Sp, t, Comma);
    private static Formula Hyp(Formula a) => Seq(a, Sp, Rightarrow);
    private static Formula Inst(string c, Formula x) => Seq(OpenBracket, Call(c, x), CloseBracket);
    private static Formula FamilyInst(string c, string x) => Seq(OpenBracket, Forall, Sp,
        V("i"), Colon, Sp, V("I"), Comma, Sp, Call(c, Call(x, V("i"))), CloseBracket);
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula[] Family(bool uniform, bool zero) => [
        Seq(All("I", V("Type")), Sp, All("X", V("Type")), Sp,
            Inst(uniform ? "UniformSpace" : "TopologicalSpace", V("X")), Sp, Inst("CompactSpace", V("X")),
            uniform ? Seq() : Inst("TTwoSpace", V("X"))),
        Seq(All("B", Map(V("I"), V("Type"))), Sp, All("Y", Map(V("I"), V("Type")))),
        Seq(Grp(), FamilyInst("MetricSpace", "B"), Sp, FamilyInst("MetricSpace", "Y"), Sp,
            FamilyInst("CompactSpace", "Y"), zero ? FamilyInst("TotallyDisconnectedSpace", "Y") : Seq()),
        Seq(All("pi", Call("DependentMap", V("I"), V("X"), V("B"))), Sp,
            All("p", Call("CoordinateMap", V("I"), V("Y"), V("B")))),
        Hyp(Call("CoordinateContinuous", V("pi"), V("p"))),
        Hyp(Call("SeparatesPoints", V("pi"))), Hyp(Call("CoordinateSurjective", V("p"))),
        Seq(All("f", Map(V("X"), V("X"))), Sp, All("d", Call("CoordinateEndomorphism", V("B"))), Sp,
            All("g", Call("CoordinateEndomorphism", V("Y")))),
        Hyp(Call("CoordinateSemiconjugacies", V("pi"), V("p"), V("f"), V("d"), V("g"))),
        Hyp(Seq(Call("HasShadowing", V("f")), Sp, Land, Sp, Call("CoordinateShadowing", V("g")), Sp, Land, Sp,
            Call("CoordinatePositiveExpansivity", V("d")))) ];

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common-source constrained product of arbitrary many actual metric extensions has shadowing under positive expansivity.",
        H("Arbitrary-Index Constrained Product"), Blocks(
        Describe.Lean(DescribeId.Create("finite-support-entourage"), DeclarationHandle.Create(Owner + "finite_support_entourage"),
            H("Every observation has finite support"), StatementSource.FromAuthor(St(
                Seq(All("I", V("Type")), Sp, All("Y", Map(V("I"), V("Type")))),
                Seq(Grp(), FamilyInst("MetricSpace", "Y")),
                Seq(All("S", Call("Set", Call("Product", V("Y")))), Sp, All("E", Call("Set", Call("Pair", V("S"))))),
                Hyp(Call("Entourage", V("S"), V("E"))),
                Seq(Exists, Sp, V("F"), Colon, Sp, Call("Finset", V("I")), Comma, Sp,
                    V("eps"), Colon, Sp, Map(V("I"), Seq(Mathbb, Grp(V("R")))), Comma),
                Seq(Call("PositiveOn", V("eps"), V("F")), Sp, Land, Sp,
                    Call("CylinderImplies", V("S"), V("F"), V("eps"), V("E"))))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "I is any set-index type, Y(i) any dependent metric family, S any product subspace, and E any entourage on S. "
                + "There are a finite F and real eps(i)>0 for i in F such that, for every a,b in S, all inequalities "
                + "dist(a(i),b(i))<eps(i) on F imply (a,b) in E. Subtype uniformity, Pi.uniformity, "
                + "Filter.HasBasis.iInf' and the metric distance basis produce this implication. Neither I nor F must be nonempty."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("constrained-product-shadowing"), DeclarationHandle.Create(Owner + "constrained_product_hasShadowing"),
            H("Shadowing in the actual constrained subspace"), StatementSource.FromAuthor(St([.. Family(true, false),
                Call("HasShadowing", Call("CommonSourceDynamics", V("pi"), V("p"), V("f"), V("d"), V("g")))])),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "CoordinateContinuous means that every pi(i):X to B(i) and p(i):Y(i) to B(i) is continuous. "
                + "CoordinateSurjective means every p(i) is onto. CoordinateSemiconjugacies asserts pi(i) f=d(i) pi(i) and p(i) g(i)=d(i) p(i). "
                + "CoordinateShadowing and CoordinatePositiveExpansivity quantify over all i. No source or coordinate dynamics is required to be onto. "
                + "The supplied metric extension spaces Y(i), their compactness and shadowing, and the positive expansive factors B(i), "
                + "are parameters. No paper extension theorem is treated as an existing Lean instance.")),
                Paragraph(Text(
                "Z consists of y in the product of Y(i) for which there exists one x with p(i)(y(i))=pi(i)(x) for every i. "
                + "Separation makes x unique. For an entourage E on Z, finite_support_entourage selects F and tolerances. "
                + "For every i in F, positive_expansivity_source_relative derives the exact-fibre tracing controls before the sequence is given. "
                + "A finite intersection of pulled-back base observations and the projection's uniform continuity give the pseudo-orbit control. "
                + "One base shadowing point x is chosen. The controlled coordinates trace in the exact fibres over pi(i)(x); "
                + "uncontrolled coordinates are filled in those same fibres by choice. Their tuple lies in Z and E-traces at every natural time."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("constrained-product-extension"), DeclarationHandle.Create(Owner + "constrained_product_extension"),
            H("Topology, projection and simultaneous whole orbits"), StatementSource.FromAuthor(St([.. Family(false, true),
                Hyp(Call("CoordinateContinuous", V("g"))),
                Seq(V("Z"), Eq, Call("CommonSource", V("pi"), V("p")), Comma, Sp,
                    V("q"), Eq, Call("CommonSourceMap", V("pi"), V("p")), Comma),
                Seq(V("G"), Eq, Call("CommonSourceDynamics", V("pi"), V("p"), V("f"), V("d"), V("g"))),
                Seq(Call("IsClosed", Call("CommonSourceSet", V("pi"), V("p"))), Sp, Land),
                Seq(Call("CompactSpace", V("Z")), Sp, Land, Sp, Call("TTwoSpace", V("Z")), Sp, Land, Sp,
                    Call("TotallyDisconnectedSpace", V("Z")), Sp, Land),
                Seq(Call("Continuous", V("q")), Sp, Land, Sp, Call("Surjective", V("q")), Sp, Land, Sp, Call("Continuous", V("G")), Sp, Land),
                Seq(Call("Semiconj", V("q"), V("G"), V("f")), Sp, Land, Sp, Call("HasShadowing", V("G")), Sp, Land),
                Call("WholeOrbitCoding", V("X"), V("I"), V("Z"), V("q"), V("G"), V("p"), V("pi"), V("f"))])),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing")), Blocks(Paragraph(Text(
                "X is compact Hausdorff; the compatible uniformity is introduced explicitly inside the proof. Each Y(i) is also totally disconnected. "
                + "The exact conclusion is a conjunction: commonSourceSet is closed; Z is compact, Hausdorff and totally disconnected; "
                + "q is continuous and onto; G is continuous; q semiconjugates G to f; and G has the existing finite-open-cover shadowing property. "
                + "WholeOrbitCoding is: for every x in X there is z in Z with q(z)=x and, for every i and every natural n including zero, "
                + "p(i)((G^n(z))(i))=pi(i)(f^n(x)). Compact Hausdorff totally disconnected spaces have the Mathlib clopen basis. "
                + "Z is the inverse image of the compact range of the separating coordinate embedding. Continuity of q follows through that embedding, "
                + "not from continuity of an arbitrary choice function. Tychonoff and ordinary choice are represented by Mathlib and Classical.choice.")),
                Paragraph(Text(
                "Empty and singleton index types, empty finite support and empty source are included. For an empty index, separation forces a nonempty source to be a singleton. "
                + "No inverse orbit or orbit-surjectivity is used. Onto factor maps pi(i), compactness and shadowing of B(i), and continuity of f and d(i) "
                + "may be added to recover the approved system telescope; the proof does not require these extra premises. "
                + "Peng Q5.1 and Q5.2 remain open here. Without positive expansivity, the unpaid obligation is one joint source point lying in every finite coordinate's prescribed-fibre tracer set, "
                + "with the control chosen before each pseudo-orbit. ALP and vertex surjectivity do not pay it. No novelty or priority is claimed."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(F.Id(name))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
}
