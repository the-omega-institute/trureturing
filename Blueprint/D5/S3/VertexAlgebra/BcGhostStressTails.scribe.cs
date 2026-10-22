using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostStressTailsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostStressTails.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/eholzer1997ghost");
    private static Formula Bound() => Call("sup", Call("occupied", F.Id("v")), F.Id("id"));
    private static Formula RingStatePrefix() => Seq(
        Forall, Sp, F.Id("K"), Colon, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("CommRing", F.Id("K")), CloseBracket, Comma, Sp,
        Forall, Sp, F.Id("v"), InMacro, Sp, Call("Fock", F.Id("K")), Comma, Sp);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual ghost stress modes have a state-dependent positive tail, making the outer ghost-stress normal ordering finite on every state.",
        H("Actual Ghost Stress Tails"),
        Blocks(
            Paragraph(Text("Let K be any commutative ring and Fock(K)=Finset(N) ->0 K. A state is an "
                + "arbitrary finite superposition of finite occupied subsets. Write B(v)=sup id "
                + "(occupied(v)), where occupied(v) is the union of the subsets in the Finsupp support. "
                + "The supremum of the empty set is zero; B(v) is cast to Z in integer bounds. "
                + "The bounds are sufficient and are not asserted to be sharp. No nontriviality, characteristic-zero or "
                + "field hypothesis is imposed on K.")),
            Paragraph(Text("Use the signed insertion and deletion operators on this full carrier. "
                + "The mode b_p creates for p<=-2 and annihilates otherwise; c_q creates for q<=1 and "
                + "annihilates otherwise. The actual normal-ordered pair is b_p c_q for p<=-2 and "
                + "minus c_q b_p otherwise. The stress operator is the statewise finite sum "
                + "L_m(v)=finsum_k (m-k) :b_(m+k)c_(-k): v, with integer coefficients cast into K.")),
            Describe.Lean(
                DescribeId.Create("bc-ghost-normal-pair-high-tail"),
                DeclarationHandle.Create(Prefix + "normal_pair_high"),
                H("Every high normal-ordered ghost pair vanishes on every state"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("K"), Colon, F.Id("Type"), Comma, Sp,
                    OpenBracket, Call("CommRing", F.Id("K")), CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("k"), InMacro, Sp,
                    Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    F.Id("v"), InMacro, Sp, Call("Fock", F.Id("K")), Comma, Sp,
                    D(2), Cdot, Bound(), Plus, D(4), Lt, F.Id("m"), Rightarrow, Sp,
                    Call("normalPair", F.Id("K"),
                        Seq(F.Id("m"), Sp, Plus, Sp, F.Id("k")),
                        Seq(Minus, F.Id("k")), F.Id("v")), Eq, D(0)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("This is the termwise tail theorem used by the expanded-array BRST support argument. "
                    + "For the actual rectangle, the term c_(-n) normalPair(n+k,-k) g when n>=-1 "
                    + "and the term normalPair(n+k,-k) c_(-n) g otherwise must be killed separately at high n. "
                    + "The theorem supplies the first factor's vanishing on every state; it is not replaced by "
                    + "the aggregate L_high_mode statement, because later support reasoning reorders the two factors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-stress-high-mode"),
                DeclarationHandle.Create(Prefix + "L_high_mode"),
                H("Positive stress modes eventually kill every state"),
                StatementSource.FromAuthor(Disp(Seq(
                    RingStatePrefix(), Forall, Sp, F.Id("m"), InMacro, Sp, Mathbb, Grp(F.Id("Z")),
                    Comma, Sp, D(2), Cdot, Bound(), Plus, D(4), Lt, F.Id("m"), Rightarrow, Sp,
                    Call("L", F.Id("K"), F.Id("m"), F.Id("v")), Eq, D(0)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every actual normal-ordered summand vanishes for this m, "
                    + "not just those in a chosen finite interval. On a basis subset S put p=m+k "
                    + "and q=-k, so p+q=m. If p<=-2, the right c_q annihilator has site "
                    + "2(q-2)>sup(S). If p>=-1, either the right b_p annihilator has site "
                    + "2(p+1)+1>sup(S), or p is small and the left c_q annihilator has site "
                    + "2(q-2)>sup(S). Deleting the b-site cannot introduce that c-site. Linearity "
                    + "extends this calculation to every state because every basis subset in its "
                    + "support has supremum at most B(v). The defining finsum is therefore zero."))),
                DescribeRole.Theorem),
            Paragraph(Text("Define outerNormalPair_n=c_(-n) composed with L_n for n>=-1, and "
                + "L_n composed with c_(-n) for n<=-2, without an additional sign. This definition names only a support "
                + "family; it does not define a complete BRST charge.")),
            Describe.Lean(
                DescribeId.Create("bc-ghost-stress-outer-finite-support"),
                DeclarationHandle.Create(Prefix + "outer_has_finite_support"),
                H("The outer normal-ordering family has finite support"),
                StatementSource.FromAuthor(Disp(Seq(
                    RingStatePrefix(), Call("HasFiniteSupport", Seq(
                        F.Id("n"), Mapsto, Call("outerNormalPair", F.Id("K"), F.Id("n"), F.Id("v"))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The support is contained in the integer interval "
                    + "[-B(v)-2,2B(v)+4]. Below its lower endpoint the right c_(-n) is deletion at "
                    + "site 2(-n-2)>B(v), which kills every basis subset of v. Above its upper "
                    + "endpoint the right L_n kills v by the positive stress tail theorem. Thus "
                    + "the actual outer family, with unrestricted integer mode indices, is finite "
                    + "on each state. This supplies a finite-support ingredient for constructing "
                    + "a charge rather than assuming that the charge sum is well-defined."))),
                DescribeRole.Theorem),
            Paragraph(Text("Eholzer-Feher-Honecker, hep-th/9708160v1, Section 2, equations "
                + "(2.7)-(2.10) and (2.15), supplies the classical fermionic ghost conventions. "
                + "Physical modes are shifted as b_m=b_math_(m+1) and c_n=c_math_(n-2). "
                + "The explicit support bounds here are derived from the actual finite-subset "
                + "operators. No proof code from the source is copied.")),
            Paragraph(Text("These bounds alone prove neither an all-state Virasoro identity nor "
                + "central charge -26, current or field sign identities, a ghost-degree law, a matter "
                + "charge, BRST nilpotence, BRST cohomology, complete string theory or AdS/CFT.")))));
}
