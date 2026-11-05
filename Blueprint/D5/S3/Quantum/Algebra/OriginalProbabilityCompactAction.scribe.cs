using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OriginalProbabilityCompactActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete original prediction rows determine reversible linear continuations with compact closure.",
        H("Original Probability Rows and Compact Continuation"),
        Blocks(Describe.Lean(DescribeId.Create("original-probability-continuation"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalProbabilityCompactAction.continuation_compact"),
            H("The actual continuation representation has compact closure"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let V be any finite-dimensional real normed vector space, Gamma any group of original reversible control words, and I the entire common future-outcome domain. A row assigns to every original word a vector in V. The linear readout read maps V injectively to all real functions on I, and the original rows span all of V. Every original row readout lies between zero and one at every future-outcome coordinate. The prefix operation on I satisfies read(row(a g))(i)=read(row(a))(prefix(g,i)). No topology or continuity of the original word group is assumed.")),
                Paragraph(Text("There exists a monoid homomorphism rho from the opposite group of Gamma into the actual units of continuous endomorphisms of the same V, with rho(op g)(row(a))=row(a g) for every a,g. Its range has compact topological closure inside that actual unit group. The opposite group records the order of right continuation: applying h and then g sends a to a h g. The conclusion does not identify distinct original words or delete their program identities; only their action on full predictions is represented.")),
                Paragraph(Text("Full-future injectivity proves well-definedness. Precomposing read(v) by a future prefix stays in the readout range, first for actual rows and then by linear span induction for every v. Its unique preimage defines a linear operator T_g. Equality on the original spanning rows proves T_1=I and T_g T_h=T_(h g). Accurate word inverses therefore give actual inverse operators, and finite dimensionality makes them continuous in the original chosen norm.")),
                Paragraph(Text("Compactness uses the full coordinate interval, including all unknown future coordinates. The set K of vectors whose entire readout lies in the product interval [0,1]^I is compact: the injective finite-dimensional readout is a closed embedding, and the product interval is compact. Evaluation of an operator on every original spanning row is another injective finite-dimensional linear map, hence a closed embedding. Operators taking every row into K consequently form a compact set C. This argument uses the product topology and does not assume that a finite sample has already captured the complete prediction space.")),
                Paragraph(Text("Both an actual continuation and its inverse preserve the row set. Embed each unit as its value and opposite inverse value. Mathlib's closed embedding of units into that product pulls the compact set C times opposite(C) back to a compact set containing the actual continuation subgroup. Its topological closure is a closed subset of that compact set, so remains compact in the unit topology. Singular ambient limits are excluded by retaining both inverse equations; no inverse bound or compactness is assumed.")),
                Paragraph(Text("This is the well-defined-continuation and compact-closure part of OMEGAQ-008 Lemma 2.2. The norm may be any norm on the same finite-dimensional full row space, since every injective readout and operator comparison used here is continuous by finite dimensionality. Probability normalization supplies the displayed coordinate bounds in a normalized common-future model; normalization and the affine mass functional are not reconstructed by this theorem. The normalized-center theorem below derives the Haar-fixed center, cyclicity and faithfulness on its mass-zero subspace. Packaging the restricted compact subgroup, original event effects, control availability and the Born representation require their respective constructions. Compact closure alone does not make every element of that closure an exactly callable original control."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-normalized-center"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalProbabilityCompactAction.centered_continuation"),
                H("Normalized center, original cyclic subspace and effective restriction"),
                StatementSource.FromAuthor(Statement(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retain all full-row, bound and prefix hypotheses, and let mass be a real linear functional on the same V satisfying mass(row(a))=1 for every original word a. The theorem constructs the same actual continuation representation rho and its compact closure H, together with a vector c of mass one fixed by every element of H. Every element of H preserves mass on all of V. The full mass-zero subspace is both the real span of all row(a)-c and the real span of the H-orbit of e=row(1)-c. If the mass-zero subspace is nonzero then e is nonzero. Any element of H acting identically on that entire subspace is the identity element of H.")),
                    Paragraph(Text("The formula uses CenteredRows(row,c) for the set of every row(a)-c and Orbit(H,e) for the set of every original unit action h(e), with h in the actual compact closure H. The kernel is the kernel of the same supplied mass functional. The last implication compares original units on all mass-zero vectors, rather than only on a selected preparation orbit. All universes of V, Gamma and I are independent. Degenerate mass-zero spaces remain in the theorem; nonzero e is stated with exactly its necessary nontriviality premise.")),
                    Paragraph(Text("Equality of two linear maps is determined on the original spanning rows. Since each continuation permutes those normalized rows, it preserves mass. The condition of preserving mass on every vector is closed in the actual unit topology, so the same condition holds on H. Average the orbit of row(1) using Mathlib's Haar measure normalized on the whole compact group. Left translation invariance fixes the integral under every original element of H. Commuting the continuous mass functional with the integral gives mass(c)=1.")),
                    Paragraph(Text("The actual linear projection P(v)=v-mass(v)c has range exactly ker(mass), and P(row(a))=row(a)-c. Mapping the original full spanning relation through P therefore gives the first span equality. Each centered original row is the action of rho(op a) on e, and all H-actions on e have mass zero, proving the orbit-span equality in both directions. If e vanished then the orbit span would vanish, contradicting a nonzero mass-zero subspace. Finally every v splits as mass(v)c plus a mass-zero vector. An element fixing c and every mass-zero vector therefore fixes all V; unit and subgroup extensionality give the actual identity.")),
                    Paragraph(Text("This supplies the fixed-center, cyclicity and effective-restriction conclusions from the original probability-row model. It does not assume an invariant comparison form, a dimension, transitivity, or group classification. The identity implication proves faithfulness of the restriction, but the continuous unit-valued restriction map and its compact image are not packaged here. The mass functional is still an explicit input; deriving it from each original normalized test and preserving all original event effects remain separate interfaces. No closure element or completed mathematical effect is asserted to be an exactly supplied original control."))), DescribeRole.Theorem))));

    private static Formula Statement(bool includeCenter = false)
    {
        Formula v=F.Id("V"), g=F.Id("Gamma"), i=F.Id("I"), row=F.Id("row"), read=F.Id("read"), prefix=F.Id("prefix"), rho=F.Id("rho");
        Formula a=F.Id("a"), h=F.Id("g"), j=F.Id("i"), c=F.Id("c"), mass=F.Id("mass"), z=F.Id("z");
        Formula closure=Call("topologicalClosure",Call("range",rho));
        Formula e=Call("sub",Call("row",D(1)),c);
        Formula center = Seq(Sp,Land,Sp,Exists,Sp,c,Colon,v,Comma,Esc,
            Call("mass",c),Eq,D(1),Sp,Land,Sp,
            Open,Forall,Sp,h,Colon,closure,Comma,Esc,Call("value",h,c),Eq,c,Close,Sp,Land,Sp,
            Open,Forall,Sp,h,Colon,closure,Comma,Esc,Forall,Sp,z,Colon,v,Comma,Esc,
            Call("mass",Call("value",h,z)),Eq,Call("mass",z),Close,Sp,Land,Sp,
            Call("span",F.Id("R"),Call("CenteredRows",row,c)),Eq,Call("ker",mass),Sp,Land,Sp,
            Call("span",F.Id("R"),Call("Orbit",closure,e)),Eq,Call("ker",mass),Sp,Land,Sp,
            Open,Call("ker",mass),Neq,Call("Bottom"),Sp,Rightarrow,Sp,e,Neq,D(0),Close,Sp,Land,Sp,
            Forall,Sp,h,Colon,closure,Comma,Esc,
            Open,Forall,Sp,z,Colon,Call("ker",mass),Comma,Esc,
            Call("value",h,Call("subtypeValue",z)),Eq,Call("subtypeValue",z),Close,
            Sp,Rightarrow,Sp,h,Eq,D(1));
        return Disp(Seq(Forall,Sp,v,Comma,g,Comma,i,Comma,Esc,
            Call("FiniteDimensionalRealNormedSpace",v),Sp,Land,Sp,Call("Group",g),Sp,Rightarrow,Sp,
            Forall,Sp,row,Colon,g,Sp,To,Sp,v,Comma,Esc,
            Forall,Sp,read,Colon,Call("LinearMap",F.Id("R"),v,Call("Functions",i,F.Id("R"))),Comma,Esc,
            Call("Injective",read),Sp,Land,Sp,Call("span",F.Id("R"),Call("range",row)),Eq,Top,Sp,Land,Sp,
            Open,Forall,Sp,a,Colon,g,Comma,Esc,Forall,Sp,j,Colon,i,Comma,Esc,
            Call("Member",Call("read",Call("row",a),j),Call("Icc",D(0),D(1))),Close,Sp,Rightarrow,Sp,
            Forall,Sp,prefix,Colon,g,Sp,To,Sp,i,Sp,To,Sp,i,Comma,Esc,
            Open,Forall,Sp,a,Comma,h,Colon,g,Comma,Esc,Forall,Sp,j,Colon,i,Comma,Esc,
            Call("read",Call("row",Seq(a,Cdot,h)),j),Eq,
            Call("read",Call("row",a),Call("prefix",h,j)),Close,Sp,Rightarrow,Sp,
            includeCenter ? Seq(Forall,Sp,mass,Colon,Call("LinearMap",F.Id("R"),v,F.Id("R")),Comma,Esc,
                Open,Forall,Sp,a,Colon,g,Comma,Esc,Call("mass",Call("row",a)),Eq,D(1),Close,
                Sp,Rightarrow,Sp) : Seq(),
            Exists,Sp,rho,Colon,Call("MonoidHom",Call("Opposite",g),Call("UnitsContinuousEnd",F.Id("R"),v)),Comma,Esc,
            Open,Forall,Sp,a,Comma,h,Colon,g,Comma,Esc,
            Call("value",Call("rho",Call("op",h)),Call("row",a)),Eq,Call("row",Seq(a,Cdot,h)),Close,
            Sp,Land,Sp,Call("IsCompact",closure),includeCenter ? center : Seq()));
    }
}
