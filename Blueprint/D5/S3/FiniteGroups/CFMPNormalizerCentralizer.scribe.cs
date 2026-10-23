using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class CFMPNormalizerCentralizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalizer quotient acts as the full centralizer of the right-coset action.",
        H("Normalizer Quotient and Right-Coset Centralizer"),
        Blocks(Describe.Lean(
            DescribeId.Create("cfmp-normalizer-centralizer"),
            DeclarationHandle.Create(
                "D5/S3/FiniteGroups/CFMPNormalizerCentralizer.normalizerCentralizerIso"),
            H("The generic right-coset centralizer theorem"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary group G and subgroup H, Omega_R is the quotient by "
                    + "QuotientGroup.rightRel H and R_a sends H g to H g a. The quotient "
                    + "group is formed inside the normalizer N_G(H), with normality of H "
                    + "there derived from the normalizer definition.")),
                Paragraph(Text(
                    "The isomorphism sends n H to F_n, where F_n(H g) = H n g. "
                    + "Standard function composition gives F_n composed with F_m = F_(n m). "
                    + "An equivariant permutation is determined by its value at H; exact "
                    + "stabilizer preservation forces that value to be H n with n in the "
                    + "normalizer. An element of H acts trivially on every right coset; "
                    + "conversely, evaluating a kernel element at H proves that it lies in H. "
                    + "Thus H.subgroupOf(N_G(H)) equals the kernel of normalizerMap. "
                    + "QuotientGroup.liftEquiv applies directly to this kernel equality "
                    + "and the surjectivity of normalizerMap to give the isomorphism.")),
                Paragraph(Text(
                    "The theorem is the generic algebraic consumer for CFMP source clauses "
                    + "122.2 and 123.1. It does not claim the concrete A5 marked Phi, the "
                    + "U,V,D arrays, a normalizer cardinality, or any topology.")),
                Paragraph(Text(
                    "[A5.1 — marked data and shared labels] Fix the alphabet correspondence "
                    + "sending source letter j to j−1 in Fin 5. Let G = A₅ = "
                    + "alternatingGroup (Fin 5), let u = (3 4 5), v = (1 3 5 2 4), and "
                    + "let H = ⟨v⟩. Products of permutations use ordinary function "
                    + "composition. The five-letter image vectors of u, v, and "
                    + "n = (2 5)(3 4) are respectively (0,1,3,4,2), (2,3,4,0,1), "
                    + "and (0,4,3,2,1).")),
                Paragraph(Text(
                    "[A5.2 — literal twelve-letter permutations] In the marked labels "
                    + "0 through 11 retain U = (1,2,0,5,3,4,7,8,6,11,9,10) and "
                    + "V = (0,2,8,7,6,10,1,5,4,3,9,11). Define D(i) = 11−i in this "
                    + "chosen labelling; D is derived here and is not attributed to the "
                    + "original source as a separately named vector.")),
                Paragraph(Text(
                    "[A5.3 — right-coset model and representatives] Let Q be the set of "
                    + "right cosets Hg, implemented as Quotient (QuotientGroup.rightRel H), "
                    + "so x and y represent the same coset precisely when yx⁻¹ ∈ H. In label "
                    + "order 0 through 11 use the representatives "
                    + "(1, u, u², u²v²u, u²v², u²vu²v, u²vu, u²vu², u²v, "
                    + "u²vu²v²u, u²vu²v², u²vu²v²u²). They satisfy separation "
                    + "rⱼrᵢ⁻¹ ∈ H iff i = j, coverage (for every g ∈ G some i has "
                    + "rᵢg⁻¹ ∈ H), and the transitions r_U(i)(rᵢu)⁻¹ ∈ H, "
                    + "r_V(i)(rᵢv)⁻¹ ∈ H, and r_D(i)(nrᵢ)⁻¹ ∈ H.")),
                Paragraph(Text(
                    "[A5.4 — shared parameter correspondence and orientation] The relations "
                    + "define the bijection Phi(i) = H rᵢ from Fin 12 to Q, with Phi(0) = H, "
                    + "and the right translations R_a(Hg) = Hga satisfy "
                    + "Phi(U(i)) = R_u(Phi(i)) and Phi(V(i)) = R_v(Phi(i)). The base-point "
                    + "stabilizer is exactly H. Since (ya)(xa)⁻¹ = yx⁻¹, each R_a is "
                    + "well defined; evaluation on a representative gives "
                    + "R_b(R_a(Hg)) = Hgab = R_ab(Hg), so R_ab = R_b composed with R_a "
                    + "under ordinary composition. The generators are neither inverted nor "
                    + "replaced by a left action.")),
                Paragraph(Text(
                    "[A5.5 — generation from the marked coverage] Put L = ⟨u,v⟩. Every "
                    + "listed representative is a word in u and v, and H = ⟨v⟩ is contained "
                    + "in L. For arbitrary g ∈ G, coverage supplies i with "
                    + "h = rᵢg⁻¹ ∈ H ≤ L, hence g = h⁻¹rᵢ ∈ L. Therefore L = G. "
                    + "This uses the existing representative coverage and no additional "
                    + "enumeration or unmarked group-isomorphism assumption.")),
                Paragraph(Text(
                    "[A5.6 — transport of the full centralizer] For a permutation p of the "
                    + "twelve labels define T(p) = Phi ∘ p ∘ Phi⁻¹. The transition relations "
                    + "give pU = Up and pV = Vp exactly when T(p) commutes with R_u and R_v. "
                    + "For a fixed permutation t of Q, K_t = {g ∈ G : t ∘ R_g = "
                    + "R_g ∘ t} is a subgroup: it contains 1; closure follows from "
                    + "R_b composed with R_a = R_ab; and inverses follow from "
                    + "R_(a⁻¹) = (R_a)⁻¹. Generation therefore gives the exact equivalence "
                    + "pU = Up and pV = Vp iff T(p) ∘ R_g = R_g ∘ T(p) for every g ∈ G.")),
                Paragraph(Text(
                    "[A5.7 — normalizer application and the D image] Apply the generic "
                    + "right-coset theorem normalizerCentralizerIso. The underlying normalizer-quotient identification is classical; this document records its repository formalization. It identifies "
                    + "N_G(H)/H, with H regarded as H.subgroupOf(N_G(H)), with the "
                    + "permutations of Q commuting with every R_g, by [n] ↦ F_n where "
                    + "F_n(Hg) = Hng. No normality of H in G is assumed; here H is not "
                    + "normal, since uvu⁻¹ ∉ H. The actual n satisfies n⁻¹vn = v⁻¹, "
                    + "n² = 1, n ∉ H, and n ∈ N_G(H). The D transition extends from the "
                    + "listed representatives to every representative: if Phi(i) = Hg, then "
                    + "Phi(D(i)) = Hng. If g and rᵢ represent the same coset, conjugating "
                    + "grᵢ⁻¹ ∈ H by n preserves H, so this formula is representative independent. "
                    + "Thus transporting [n] through Phi gives the literal map i ↦ 11−i, "
                    + "and D(0) = 11 distinguishes it from the identity.")),
                Paragraph(Text(
                    "[A5.8 — cardinality and exact conclusion] The order of v is 5, so |H| = 5; "
                    + "the normalizer has order 10. The index-times-cardinality formula, with "
                    + "H as a subgroup of its normalizer, gives |N_G(H)/H| = 2. The generic "
                    + "isomorphism and the transport equivalence consequently give cardinality "
                    + "two for the full centralizer of literal U and V, with the two elements "
                    + "identified explicitly: pU = Up and pV = Vp iff p = id or, for every i, "
                    + "p(i) = 11−i.")),
                Paragraph(Text(
                    "[A5.9 — scope and limits] This application concerns the marked finite "
                    + "permutation action and its full permutation centralizer. It does not "
                    + "establish genus, topology, geometric existence or local-chart assertions "
                    + "of §§42.3 and 122.3, or a classification of simplicial automorphisms that "
                    + "permit local relabelling. It does not complete the four CFMP theories or "
                    + "§§1–125."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula g = F.Id("G"), h = F.Id("H");
        Formula normalizer = Call("normalizer", h);
        Formula quotient = Call("quotientGroup", normalizer,
            Call("subgroupOf", h, normalizer));
        Formula omega = Call("rightCosetQuotient", h);
        Formula centralizer = Call("centralizerOfRightTranslations", omega, g);
        Formula body = Call("MulEquiv", quotient, centralizer);
        body = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("H"), Call("Subgroup", g))],
            body);
        body = new Formula.TypeArrow(Call("Group", g), body);
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("G"), F.Id("Typeu"))],
            body));
    }
}
