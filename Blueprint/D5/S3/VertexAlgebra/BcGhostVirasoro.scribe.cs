using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostVirasoroDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostVirasoro.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/eholzer1997ghost");
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rings() => Seq(
        Forall, Sp, F.Id("K"), Colon, F.Id("Type"), Caret, Grp(F.Id("u")), Comma, Sp,
        OpenBracket, Call("CommRing", F.Id("K")), CloseBracket, Comma, Esc);
    private static Formula Mode(Formula index) => Call("L", F.Id("K"), index);
    private static Formula IntegerCoefficient() => Seq(
        Open, Open, Minus, D(1, 3), Star,
        Open, F.Id("m"), Caret, Grp(D(3)), Minus, F.Id("m"), Close,
        Slash, D(6), Colon, Integers(), Close, Colon, F.Id("K"), Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every pair of original ghost stress operators satisfies the full Virasoro bracket with an integer-quotient central scalar over every commutative ring.",
        H("The Original All-State Integral Ghost Virasoro Relation"),
        Blocks(
            Paragraph(Text("At any universe u let K : Type u have [CommRing K]. "
                + "All operators in the statement are the original "
                + "BcGhostFockSupport.L acting in Module.End K (Fock K), where "
                + "Fock K is the signed finite-subset algebraic carrier with no "
                + "global mode cutoff. Products are endomorphism composition, "
                + "rightmost first. id denotes LinearMap.id on exactly this "
                + "carrier. The notation ite(test,x,y) denotes if test then x "
                + "else y. The theorem assumes no Virasoro representation, "
                + "central-charge relation, field, nontriviality, characteristic "
                + "or inverse of six.")),
            Describe.Lean(
                DescribeId.Create("bc-ghost-virasoro-integral-bracket"),
                DeclarationHandle.Create(Prefix + "L_virasoro"),
                H("The full original stress bracket has the exact integral central term"),
                StatementSource.FromAuthor(Disp(Seq(Rings(),
                    Forall, Sp, F.Id("m"), Colon, Integers(), Comma, Sp,
                    Forall, Sp, F.Id("n"), Colon, Integers(), Comma, Esc,
                    Mode(F.Id("m")), Star, Mode(F.Id("n")), Minus,
                    Mode(F.Id("n")), Star, Mode(F.Id("m")), Eq,
                    Open, F.Id("m"), Minus, F.Id("n"), Colon, F.Id("K"), Close,
                    Cdot, Mode(Seq(F.Id("m"), Plus, F.Id("n"))), Plus,
                    Call("ite", Seq(F.Id("m"), Plus, F.Id("n"), Eq, D(0)),
                        IntegerCoefficient(), D(0)), Cdot, Sp, F.Id("id")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The complete original telescope is {K : Type u} "
                        + "[CommRing K] (m n : Int). Its exact conclusion is "
                        + "L (K := K) m * L n - L n * L m = "
                        + "(m-n : K) smul L(m+n) + "
                        + "(if m+n=0 then ((-13*(m^3-m)/6 : Int) : K) else 0) "
                        + "smul LinearMap.id. Division is carried out in Int "
                        + "before casting into K, including at negative m. "
                        + "The conditional is the delta(m+n=0) central term. "
                        + "This is the unscaled equality of full operators "
                        + "for every pair of integers, not a vacuum-only "
                        + "identity or a field-only rational-six version.")),
                    Paragraph(Text("The live proof forms the defect "
                        + "D=L_m L_n-L_n L_m-(m-n) smul L_(m+n). Its private "
                        + "defect_commutes calculation uses the associative "
                        + "Lie bracket and the original stress-current "
                        + "covariance. For a family X with "
                        + "[L_a,X_t]=(weight*a-t) smul X_(a+t), the Jacobi "
                        + "expansion leaves a scalar polynomial that is zero. "
                        + "Using X=b with weight=1 and X=c with weight=-2 "
                        + "proves the actual defect commutes with every b "
                        + "and c mode. These weights are the covariance "
                        + "coefficients in this calculation. The original "
                        + "mode_commutant_scalar then makes D the scalar "
                        + "given by the empty-subset coefficient of D vacuum.")),
                    Paragraph(Text("That scalar is computed, not assumed. Insertion "
                        + "cannot produce the empty subset, so every L_t vacuum "
                        + "has zero empty coordinate. Deleting a one-creator "
                        + "vacuum vector reaches that coordinate only at "
                        + "matching mode indices. Stress-current covariance "
                        + "and the original finite support interval therefore "
                        + "give (L_m(L_n vacuum)) emptyset=0 whenever m+n "
                        + "is nonzero. Both orders of the off-diagonal "
                        + "commutator have zero empty coordinate.")),
                    Paragraph(Text("When n=-m and m>0, "
                        + "L_vacuum_annihilation kills L_m vacuum and "
                        + "L_vacuum_contraction computes L_m(L_(-m) vacuum) "
                        + "with the integer quotient -13(m^3-m)/6. At m=0 "
                        + "the commutator and cubic both vanish. At m<0 "
                        + "the reverse product is evaluated using the "
                        + "positive index -m. The proof first establishes "
                        + "6 divides -13(m^3-m) by the six integer residue "
                        + "classes; Int.neg_ediv_of_dvd then justifies "
                        + "negating that exact integer quotient. Hence the "
                        + "same central scalar is obtained for negative "
                        + "m without an invalid sign rule for arbitrary "
                        + "integer division. Substituting this scalar into "
                        + "the ghost-End commutant equality gives the "
                        + "full operator bracket on every original state."))),
                DescribeRole.Theorem),
            Paragraph(Text("The existing eholzer1997ghost library note compares "
                + "the weight-(2,-1) conventions with the conventional label "
                + "central charge -26. It is acknowledged as background, "
                + "not as proof of this exact ring-parametric implementation "
                + "theorem. The operator construction and derivation are "
                + "repository-derived. No tensor-End factorization, "
                + "literature novelty, BRST cohomology, no-ghost theorem, "
                + "complete physical/string result or AdS completion "
                + "is claimed.")))));
}
