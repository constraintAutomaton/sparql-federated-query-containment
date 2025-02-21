# Query containment federated queries semantic

We have three use cases that we can divide into two.
When the whole query is sent to each sources and when a sub-queries are sent to sources.
When sub-queries are sent to sources we can divide this case into two; when the sub-queries and data sources are defined 
in the query and when the query engine do the source selection and the query division.

# Preliminaries
Given a query $Q$ and data sources $D1$, $D2$, $D3$, where all $Di$ are set semantics.
We denote the execution of a query over a data source $Q^{Di}$.

When a query is performed to an endpoint by default, it is sent triple by triples.
We denote this execution by $Q_{tp}^{Di}$.
This default case does not apply when the query to be sent is specified by the user using a `SERVICE` clause 
or when the source selection algorithm decided to send more complex queries.

The query processing operates in two steps.
In the first step, the query $Qi$ is processed over a data source $Di$ to produce a database $D_{b}i$ of bindings with a bag semantic.
Then, we perform the join over the bindings to return the final results binging operating in bag semantic.
We consider it two steps because multiple queries are performed over different data sources and are joined together.

# Sending the whole query into a source

$Q^{(D1, D2, D3)} =  Q_{tp}^{D1} \bowtie Q_{tp}^{D2} \bowtie Q_{tp}^{D3} = Q^{D}$

where $D = D1 \uplus D2 \uplus D3$

Given that $Q$ is processed in each data source $Di$ triple by triple, then
for each data source $Di$ we get a binding database $D_{b}i$ after performing the query.
After the queries $Q_{tp}$ are performed, the query $Q$ is performs over the bag union of the $D_{b}i$, that we denote $D_{b}$.
Since the query was performed triple pattern by triple pattern we for each data source $Di$ it is the equivalent of getting 
a $Di^{\prime} \subset Di$ without the triple that we know will not be query relevant, furthermore since the results of this 
operation is in bag semantic it allows duplicates. 
Thus, we know that performing the query $Q$ over a bag semantic database $D$ will produce the same results as 
performing the query with multiple sources.







# With service clauses
We suppose that there are 3 service calls with the subqueries $Q_1$, $Q_2$, $Q_3$ and
By default, when a query is performed to an endpoint, it is sent triple by triples.
It is not the case when it is specified by the user or when a source selection algorithm decides to send a bigger query.the body of the query $Q_{body}$ called on the "main" endpoint $D0$.

So the execution is

$Q^{(D1, D2, D3)} = Q_1^{D1} \bowtie Q_2^{D2} \bowtie Q_3^{D3} \bowtie Q_{body}^{D0}$

Where all the execution was done over a set semantic database with a bag semantic query. Given a different query has been sent to a different endpoint we cannot consider $(D1, D2, D3)$ has
one data source, we can only link them via the binding results. I am unsure if we can create a concept of doing one query over a single database with a specific semantic and I do not know how to manage the join operation of those queries when considering possible duplicate in those $Di$


# Without service clause
We send the whole query to the different endpoints and do the union of the results.

$Q^{(D1, D2, D3)} =  Q^{D1} \cup Q^{D2} \cup Q^{D3} = Q^{D}$

where $D = D1 \uplus D2 \uplus D3$

Why?

$D1$, $D2$, and $D3$ can have be duplicates when considered as a whole (has one dataset).
So, the execution algorithm can encounter the same triples multiple times.
The equation linking all the queries make the unions of the results in a bag semantic manner (because of SPARQL and we are dealing with bindings). Thus, we would get the same results if we were to query one data source with a bag semantic.