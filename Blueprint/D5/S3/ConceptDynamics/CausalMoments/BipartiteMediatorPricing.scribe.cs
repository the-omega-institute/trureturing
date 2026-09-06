using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class BipartiteMediatorPricingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.";
    private static Formula Pi => V("coupling");
    private static Formula Color => V("color");
    private static Formula Table => V("table");
    private static Formula Mult => V("multiplier");
    private static Formula K => V("certificate");
    private static Formula Law => V("law");
    private static Formula Candidate => V("candidate");
    private static Formula I => V("i");
    private static Formula J => V("j");
    private static Formula Tau => V("normalizationMultiplier");
    private static Formula Mass(Formula i, Formula j) => C("mass",Pi,C("pair",i,j));
    private static Formula Bit(Formula y, Formula i) => C("ite",C("apply",y,i),One,Z);
    private static Formula Flip(Formula y) => C("flipTable",Color,y);
    private static Formula Field => C("pricingField",Pi,Mult,I);
    private static Formula Switched => C("switchedField",Pi,Color,Mult,I);
    private static Formula Cap => C("pricingCapacity",Pi);
    private static Formula Src => C("pricingSourceCapacity",Pi,Color,Mult);
    private static Formula Snk => C("pricingSinkCapacity",Pi,Color,Mult);
    private static Formula Offset => C("pricingOffset",Pi,Color,Mult);
    private static Formula Price(Formula y) => C("completeMediatorPricingScore",Pi,Mult,y);
    private static Formula Best => C("certifiedPricingValue",Pi,Color,Mult,K);
    private static Formula Bipartite => C("OffDiagonalBipartite",Pi,Color);
    private static Formula Checked => B(C("checkBipartitePricing",Pi,Color,Mult,K),Eq,V("true"));
    private static Formula E(Formula f, Formula law) => C("linearObjective",f,C("mass",law));
    private static Formula Mean(Formula law, Formula i) => E(Lam("table",Bit(Table,i)),law);
    private static Formula Benefit(Formula law) => C("completeMediatorBenefit",Pi,law);
    private static Formula Means(Formula law) => All("i",B(Mean(law,I),Eq,C("probability",I)));
    private static Formula RowTerm => SumF("i",B(C("multiplier",I),Cdot,C("probability",I)));
    private static Formula ValueSet => C("setOf",Lam("value",ExistsF("law",And(Means(Law),B(Benefit(Law),Eq,V("value"))))));
    private static Formula Half(Formula x) => Seq(Frac,Grp(x),Grp(F.D(2)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual complete-mediator pricing is reduced to a checked minimum cut, and the same certificate closes the full outcome-marginal master problem.", H("BipartiteMediatorPricing"), Blocks(
            Paragraph(Text("Mediator is an arbitrary finite type with decidable equality. coupling is the existing normalized rational law on Mediator times Mediator. color and table map Mediator to Bool; multiplier and probability map Mediator to Q; law and candidate are existing FiniteResponseLaw values on complete Boolean tables. certificate is the existing STCutCertificate. All formula quantifiers carry these types; finite sums cover every indicated carrier. The selected graph condition concerns the off-diagonal support of coupling.")),
            Describe.Lean(DescribeId.Create("off-diagonal-bipartite"), DeclarationHandle.Create(Prefix + "OffDiagonalBipartite"),
                H("Color the actual off-diagonal support"), StatementSource.FromAuthor(Disp(All("Mediator coupling color",B(Bipartite,Leftrightarrow,All("i j",B(And(B(I,Neq,J),B(Mass(I,J),Neq,Z)),Rightarrow,B(C("color",I),Neq,C("color",J)))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The graph is the cross-world mediator coupling support, not the causal DAG. Diagonal mass is allowed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("flip-table"), DeclarationHandle.Create(Prefix + "flipTable"),
                H("A bijective color-class flip"), StatementSource.FromAuthor(Disp(All("Mediator color table i",B(C("flipTable",Color,Table,I),Eq,C("ite",C("color",I),C("not",C("table",I)),C("table",I)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each complete table remains an actual response table after the deterministic flip."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("flip-table-involutive"), DeclarationHandle.Create(Prefix + "flipTable_involutive"),
                H("Recover every original column"), StatementSource.FromAuthor(Disp(All("Mediator color table",B(Flip(Flip(Table)),Eq,Table)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The involution ensures the cut optimization covers all original columns."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("off-diagonal-mass"), DeclarationHandle.Create(Prefix + "offDiagonalMass"),
                H("Remove harmless loop mass"), StatementSource.FromAuthor(Disp(All("Mediator coupling",B(C("offDiagonalMass",Pi),Eq,SumF("pair",C("ite",B(C("fst",V("pair")),Neq,C("snd",V("pair"))),C("mass",Pi,V("pair")),Z)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Loops never generate benefit and must not be included in the constant cut offset."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pricing-field"), DeclarationHandle.Create(Prefix + "pricingField"),
                H("Retain the full vertex field"), StatementSource.FromAuthor(Disp(All("Mediator coupling multiplier i",B(Field,Eq,B(B(C("rightResponseMarginal",C("mass",Pi),I),Minus,C("leftResponseMarginal",C("mass",Pi),I)),Minus,B(F.D(2),Cdot,C("multiplier",I))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the actual field in the previously proved pricing identity, with no stationarity assumption."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("switched-field"), DeclarationHandle.Create(Prefix + "switchedField"),
                H("Signed field after the flip"), StatementSource.FromAuthor(Disp(All("Mediator coupling color multiplier i",B(Switched,Eq,C("ite",C("color",I),B(Z,Minus,Field),Field))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The color class changes the sign of its vertex field."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pricing-capacity"), DeclarationHandle.Create(Prefix + "pricingCapacity"),
                H("Nonnegative internal capacities"), StatementSource.FromAuthor(Disp(All("Mediator coupling i j",B(C("pricingCapacity",Pi,I,J),Eq,B(Mass(I,J),Plus,Mass(J,I)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both directions are retained. Each actual cut counts only the direction crossing from true to false."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pricing-source-capacity"), DeclarationHandle.Create(Prefix + "pricingSourceCapacity"),
                H("Source terminal capacity"), StatementSource.FromAuthor(Disp(All("Mediator coupling color multiplier i",B(C("pricingSourceCapacity",Pi,Color,Mult,I),Eq,C("max",Z,Switched))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive switched field penalizes placement on the sink side."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pricing-sink-capacity"), DeclarationHandle.Create(Prefix + "pricingSinkCapacity"),
                H("Sink terminal capacity"), StatementSource.FromAuthor(Disp(All("Mediator coupling color multiplier i",B(C("pricingSinkCapacity",Pi,Color,Mult,I),Eq,C("max",Z,B(Z,Minus,Switched)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The negative switched field penalizes placement on the source side."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pricing-offset"), DeclarationHandle.Create(Prefix + "pricingOffset"),
                H("All additive constants"), StatementSource.FromAuthor(Disp(All("Mediator coupling color multiplier",B(Offset,Eq,B(B(C("offDiagonalMass",Pi),Plus,SumF("i",C("ite",C("color",I),Field,Z))),Plus,SumF("i",C("pricingSourceCapacity",Pi,Color,Mult,I))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retaining these constants is essential to compute the original reduced cost, including its factor of two."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pricing-cut-identity"), DeclarationHandle.Create(Prefix + "pricing_cut_identity"),
                H("Original pricing equals offset minus cut"), StatementSource.FromAuthor(Disp(All("Mediator coupling color table multiplier",B(Bipartite,Rightarrow,B(B(F.D(2),Cdot,Price(Flip(Table))),Eq,B(Offset,Minus,C("stCutValue",Cap,Src,Snk,Table))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equality holds on every complete table. It retains asymmetric mediator masses, arbitrary dual multipliers and loop handling."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("check-bipartite-pricing"), DeclarationHandle.Create(Prefix + "checkBipartitePricing"),
                H("Check the graph contract and optimal flow"), StatementSource.FromAuthor(Disp(All("Mediator coupling color multiplier certificate",B(C("checkBipartitePricing",Pi,Color,Mult,K),Eq,C("and",C("decide",Bipartite),C("checkSTCutCertificate",Cap,Src,Snk,K)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both tests are on the actual input; a claimed bipartite shape or solver optimality status is insufficient."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certified-pricing-value"), DeclarationHandle.Create(Prefix + "certifiedPricingValue"),
                H("Return to the original scale"), StatementSource.FromAuthor(Disp(All("Mediator coupling color multiplier certificate",B(Best,Eq,Half(B(Offset,Minus,C("flowValue",K))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The value is recomputed from the checked flow and the original coefficient offset."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checked-pricing-is-greatest"), DeclarationHandle.Create(Prefix + "checked_pricing_isGreatest"),
                H("A real column and a global maximum"), StatementSource.FromAuthor(Disp(All("Mediator coupling color multiplier certificate",B(Checked,Rightarrow,And(B(Price(Flip(C("side",K))),Eq,Best),C("IsGreatest",C("range",C("completeMediatorPricingScore",Pi,Mult)),Best)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The flipped cut realizes the global price bound. The conclusion covers every Boolean column, without enumerating them in the checker."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("checked-no-improving-column-iff"), DeclarationHandle.Create(Prefix + "checked_no_improving_column_iff"),
                H("Exact stopping criterion"), StatementSource.FromAuthor(Disp(All("Mediator coupling color multiplier certificate normalizationMultiplier",B(Checked,Rightarrow,B(All("table",B(Price(Table),Le,Tau)),Leftrightarrow,B(Best,Le,Tau)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the full no-positive-reduced-cost condition, not a test only on already generated columns."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-mediator-benefit-eq-pricing-expectation"), DeclarationHandle.Create(Prefix + "completeMediatorBenefit_eq_pricing_expectation"),
                H("Rejoin the original causal objective"), StatementSource.FromAuthor(Disp(All("Mediator coupling multiplier law",B(Benefit(Law),Eq,B(E(C("completeMediatorPricingScore",Pi,Mult),Law),Plus,SumF("i",B(C("multiplier",I),Cdot,Mean(Law,I)))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This expectation identity holds on any fixed coupling, with no bipartite or fair-marginal premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pricing-bound-implies-causal-bound"), DeclarationHandle.Create(Prefix + "pricing_bound_implies_causal_bound"),
                H("Bound every canonical outcome law"), StatementSource.FromAuthor(Disp(All("Mediator coupling multiplier probability bound law",B(And(All("table",B(Price(Table),Le,V("bound"))),Means(Law)),Rightarrow,B(Benefit(Law),Le,B(V("bound"),Plus,RowTerm)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Normalization and the original marginal rows transport the global column bound to a causal upper bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("checked-restricted-master-is-greatest"), DeclarationHandle.Create(Prefix + "checked_restricted_master_isGreatest"),
                H("Certify the full sharp endpoint"), StatementSource.FromAuthor(Disp(All("Mediator coupling color multiplier probability normalizationMultiplier certificate candidate",B(And(Checked,B(Best,Le,Tau),Means(Candidate),B(Benefit(Candidate),Eq,B(Tau,Plus,RowTerm))),Rightarrow,C("IsGreatest",ValueSet,Benefit(Candidate)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A feasible restricted-master candidate with exact primal/dual equality becomes an attaining law for the full canonical problem when the global pricing check passes. The mediator coupling is fixed throughout."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Z => F.D(0);
    private static Formula One => F.D(1);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula B(Formula x, Formula op, Formula y) => Seq(P(x), Sp, op, Sp, P(y));
    private static Formula All(string names, Formula body) => Quantify(Forall, names, body);
    private static Formula ExistsF(string names, Formula body) => Quantify(Exists, names, body);
    private static Formula Lam(string names, Formula body) => Quantify(LambdaLower, names, body);
    private static Formula SumF(string index, Formula body) => Seq(F.Sum, Underscore, Grp(V(index)), Sp, P(body));
    private static Formula Quantify(Formula q, string names, Formula body)
    {
        var a = new List<Formula> { q, Sp };
        foreach (var name in names.Split(' ')) a.AddRange([V(name), Comma, Sp]);
        a.Add(body); return Seq([.. a]);
    }
    private static Formula And(params Formula[] xs)
    {
        var a = new List<Formula>();
        for (var k=0; k<xs.Length; k++) { if (k>0) a.AddRange([Sp,Land,Sp]); a.Add(P(xs[k])); }
        return Seq([.. a]);
    }
    private static Formula C(string name, params Formula[] xs)
    {
        var a = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var k=0; k<xs.Length; k++) { if (k>0) a.AddRange([Comma,Sp]); a.Add(xs[k]); }
        a.Add(Close); return Seq([.. a]);
    }
}
