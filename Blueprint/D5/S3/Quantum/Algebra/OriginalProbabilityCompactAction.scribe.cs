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
                Paragraph(Text("This is the well-defined-continuation and compact-closure part of OMEGAQ-008 Lemma 2.2. The norm may be any norm on the same finite-dimensional full row space, since every injective readout and operator comparison used here is continuous by finite dimensionality. Probability normalization supplies the displayed coordinate bounds in a normalized common-future model; normalization and the affine mass functional are not reconstructed by this theorem. The normalized-center theorem below derives the Haar-fixed center, cyclicity and faithfulness on its mass-zero subspace. It also packages the restricted compact subgroup; original event effects, control availability and the Born representation require further constructions. Compact closure alone does not make every element of that closure an exactly callable original control."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-normalized-center"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalProbabilityCompactAction.centered_continuation"),
                H("Normalized center, original cyclic subspace and effective restriction"),
                StatementSource.FromAuthor(Statement(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retain all full-row, bound and prefix hypotheses, and let mass be a real linear functional on the same V satisfying mass(row(a))=1 for every original word a. The theorem constructs the same actual continuation representation rho and its compact closure H, together with a vector c of mass one fixed by every element of H. Every element of H preserves mass on all of V. The full mass-zero subspace is both the real span of all row(a)-c and the real span of the H-orbit of e=row(1)-c. If the mass-zero subspace is nonzero then e is nonzero. Any element of H acting identically on that entire subspace is the identity element of H.")),
                    Paragraph(Text("The formula uses CenteredRows(row,c) for the set of every row(a)-c and Orbit(H,e) for the set of every original unit action h(e), with h in the actual compact closure H. The kernel is the kernel of the same supplied mass functional. The last implication compares original units on all mass-zero vectors, rather than only on a selected preparation orbit. All universes of V, Gamma and I are independent. Degenerate mass-zero spaces remain in the theorem; nonzero e is stated with exactly its necessary nontriviality premise.")),
                    Paragraph(Text("Equality of two linear maps is determined on the original spanning rows. Since each continuation permutes those normalized rows, it preserves mass. The condition of preserving mass on every vector is closed in the actual unit topology, so the same condition holds on H. Average the orbit of row(1) using Mathlib's Haar measure normalized on the whole compact group. Left translation invariance fixes the integral under every original element of H. Commuting the continuous mass functional with the integral gives mass(c)=1.")),
                    Paragraph(Text("The actual linear projection P(v)=v-mass(v)c has range exactly ker(mass), and P(row(a))=row(a)-c. Mapping the original full spanning relation through P therefore gives the first span equality. Each centered original row is the action of rho(op a) on e, and all H-actions on e have mass zero, proving the orbit-span equality in both directions. If e vanished then the orbit span would vanish, contradicting a nonzero mass-zero subspace. Finally every v splits as mass(v)c plus a mass-zero vector. An element fixing c and every mass-zero vector therefore fixes all V; unit and subgroup extensionality give the actual identity.")),
                    Paragraph(Text("This supplies the fixed-center, cyclicity and effective-restriction conclusions from the original probability-row model. It does not assume an invariant comparison form, a dimension, transitivity, or group classification. The theorem packages a continuous injective homomorphism r from H into the actual units of continuous endomorphisms of ker(mass). For every g and every mass-zero vector v, the inclusion of r(g)v into V is exactly the original g(v). Its range is compact. Continuity follows by evaluating the restricted operator on every mass-zero vector: this evaluation is an injective linear closed embedding in finite dimensions, and each included vector varies continuously under the original action. Both value and inverse value vary continuously, giving continuity in the actual units topology. The mass functional is still an explicit input; deriving it from each original normalized test and preserving all original event effects remain separate interfaces. No closure element or completed mathematical effect is asserted to be an exactly supplied original control."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-original-probability-frontend"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalProbabilityCompactAction.probability_frontend"),
                H("Normalized original tests supply the entire effective compact frontend"),
                StatementSource.FromAuthor(Statement(true,true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the same finite-dimensional full row space V, original reversible word group Gamma and complete future-outcome domain I, with injective linear readout and spanning original rows. Let F be a nonempty family of original terminal requests, O(f) its arbitrary outcome type, and label(f,j) its original address in I. Every address in I must be supplied by some such label. For every original row and every request, all probabilities are nonnegative and the unordered sum over all its outcomes is exactly one. No finite or countable outcome assumption is imposed. The same full-future prefix equation is retained.")),
                    Paragraph(Text("The theorem constructs a real linear mass functional, equal to one on every original row. For every vector v in the entire V and every original request f, the original outcome readouts have a convergent sum equal to mass(v). It then constructs the actual continuation representation, compact closure, normalized Haar-fixed center, full mass-zero cyclic space and faithful continuous unit-valued restriction with compact image. All conclusions of the normalized-center theorem are present with this constructed mass. In the formula, TestReadout(read,v,label,f) denotes the function j maps to read(v)(label(f,j)), DependentLabels(F,O,I) denotes a family label(f):O(f) to I, and the notation for CenteredRows and Orbit is exactly as in that theorem.")),
                    Paragraph(Text("The normalization bridge uses the same full spanning relation. Simultaneously for every request, every original row has sum one. Span induction shows that every vector has a common sum for all requests: zero has sum zero, addition adds the sums, and real scaling scales them. Choose any request to compare these common sums. Uniqueness of convergent real sums proves additivity and homogeneity, producing the actual mass functional; the choice of request changes no value. Normalization of each original row follows by the same uniqueness theorem.")),
                    Paragraph(Text("For any original address choose its actual request and outcome. The singleton partial sum is at most that request's full sum, since every other probability is nonnegative. Thus every complete row coordinate lies in [0,1], supplying the bounds needed for compact continuation. The preceding theorem is applied to these derived bounds and this derived mass; compactness, normalization, a center or a faithful smaller representation are not extra premises.")),
                    Paragraph(Text("This establishes the finite-dimensional effective compact probability frontend of OMEGAQ-008 Definition 2.1 and Lemma 2.2, preserving original future addresses, labels, row values and right-word order. The constructed subgroup acts on the actual kernel of the constructed mass functional. The theorem does not turn a closure element into an exactly callable original word, supply missing tests or coherent references, or construct the later Pauli/Born representation. Those operational and amplitude interfaces retain their separate hypotheses. It is an ordinary conditional mathematical statement about the declared original row model."))), DescribeRole.Theorem))));

    private static Formula Statement(bool includeCenter = false, bool fromProbability = false)
    {
        Formula v=F.Id("V"), g=F.Id("Gamma"), i=F.Id("I"), row=F.Id("row"), read=F.Id("read"), prefix=F.Id("prefix"), rho=F.Id("rho");
        Formula a=F.Id("a"), h=F.Id("g"), j=F.Id("i"), c=F.Id("c"), mass=F.Id("mass"), z=F.Id("z");
        Formula f=F.Id("f"), tests=F.Id("F"), outcomes=F.Id("O"), label=F.Id("label"), k=F.Id("j");
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
            Open,Forall,Sp,h,Colon,closure,Comma,Esc,
            Open,Forall,Sp,z,Colon,Call("ker",mass),Comma,Esc,
            Call("value",h,Call("subtypeValue",z)),Eq,Call("subtypeValue",z),Close,
            Sp,Rightarrow,Sp,h,Eq,D(1),Close,Sp,Land,Sp,
            Exists,Sp,F.Id("r"),Colon,
            Call("MonoidHom",closure,Call("UnitsContinuousEnd",F.Id("R"),Call("ker",mass))),Comma,Esc,
            Call("Continuous",F.Id("r")),Sp,Land,Sp,Call("Injective",F.Id("r")),Sp,Land,Sp,
            Open,Forall,Sp,h,Colon,closure,Comma,Esc,Forall,Sp,z,Colon,Call("ker",mass),Comma,Esc,
            Call("subtypeValue",Call("value",Call("r",h),z)),Eq,
            Call("value",h,Call("subtypeValue",z)),Close,Sp,Land,Sp,
            Call("IsCompact",Call("range",F.Id("r"))));
        Formula bounds = fromProbability ? Seq(
            Open,Forall,Sp,a,Colon,g,Comma,Esc,Forall,Sp,j,Colon,i,Comma,Esc,
            D(0),Le,Call("read",Call("row",a),j),Close,Sp,Land,Sp,
            Open,Forall,Sp,j,Colon,i,Comma,Esc,Exists,Sp,f,Colon,tests,Comma,Esc,
            Exists,Sp,k,Colon,Call("O",f),Comma,Esc,Call("label",f,k),Eq,j,Close,Sp,Land,Sp,
            Open,Forall,Sp,a,Colon,g,Comma,Esc,Forall,Sp,f,Colon,tests,Comma,Esc,
            Call("HasSum",Call("TestReadout",read,Call("row",a),label,f),D(1)),Close)
            : Seq(Open,Forall,Sp,a,Colon,g,Comma,Esc,Forall,Sp,j,Colon,i,Comma,Esc,
                Call("Member",Call("read",Call("row",a),j),Call("Icc",D(0),D(1))),Close);
        Formula massBinder = fromProbability ? Seq(
            Exists,Sp,mass,Colon,Call("LinearMap",F.Id("R"),v,F.Id("R")),Comma,Esc,
            Open,Forall,Sp,a,Colon,g,Comma,Esc,Call("mass",Call("row",a)),Eq,D(1),Close,Sp,Land,Sp,
            Open,Forall,Sp,z,Colon,v,Comma,Esc,Forall,Sp,f,Colon,tests,Comma,Esc,
            Call("HasSum",Call("TestReadout",read,z,label,f),Call("mass",z)),Close,Sp,Land,Sp)
            : includeCenter ? Seq(Forall,Sp,mass,Colon,Call("LinearMap",F.Id("R"),v,F.Id("R")),Comma,Esc,
                Open,Forall,Sp,a,Colon,g,Comma,Esc,Call("mass",Call("row",a)),Eq,D(1),Close,
                Sp,Rightarrow,Sp) : Seq();
        return Disp(Seq(Forall,Sp,v,Comma,g,Comma,i,Comma,Esc,
            Call("FiniteDimensionalRealNormedSpace",v),Sp,Land,Sp,Call("Group",g),Sp,Rightarrow,Sp,
            fromProbability ? Seq(Forall,Sp,tests,Comma,outcomes,Comma,Esc,
                Call("FamilyOfOutcomeTypes",outcomes,tests),Sp,Land,Sp,Call("Nonempty",tests),Sp,Rightarrow,Sp,
                Forall,Sp,label,Colon,Call("DependentLabels",tests,outcomes,i),Comma,Esc) : Seq(),
            Forall,Sp,row,Colon,g,Sp,To,Sp,v,Comma,Esc,
            Forall,Sp,read,Colon,Call("LinearMap",F.Id("R"),v,Call("Functions",i,F.Id("R"))),Comma,Esc,
            Call("Injective",read),Sp,Land,Sp,Call("span",F.Id("R"),Call("range",row)),Eq,Call("Top"),Sp,Land,Sp,
            bounds,Sp,Rightarrow,Sp,
            Forall,Sp,prefix,Colon,g,Sp,To,Sp,i,Sp,To,Sp,i,Comma,Esc,
            Open,Forall,Sp,a,Comma,h,Colon,g,Comma,Esc,Forall,Sp,j,Colon,i,Comma,Esc,
            Call("read",Call("row",Seq(a,Sp,Cdot,Sp,h)),j),Eq,
            Call("read",Call("row",a),Call("prefix",h,j)),Close,Sp,Rightarrow,Sp,
            massBinder,
            Exists,Sp,rho,Colon,Call("MonoidHom",Call("Opposite",g),Call("UnitsContinuousEnd",F.Id("R"),v)),Comma,Esc,
            Open,Forall,Sp,a,Comma,h,Colon,g,Comma,Esc,
            Call("value",Call("rho",Call("op",h)),Call("row",a)),Eq,Call("row",Seq(a,Sp,Cdot,Sp,h)),Close,
            Sp,Land,Sp,Call("IsCompact",closure),includeCenter ? center : Seq()));
    }
}
