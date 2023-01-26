
# Reasoner-Guided GPT3 Completion

This post is a step-by-step instruction to perform a reasoner-guided GPT3 completion.

The example is from a medium post https://medium.com/p/4528960b0141/edit

It is about leveraging Coq to write a logic reasoning structure, then use GPT3 to flesh out the reasoning process into a text. 

Now, this guide will help you navigate between the [Reasoner Coq website](https://coq.vercel.app/) and the [OpenAI GPT3 playground](https://beta.openai.com/playground) to complete a student's task of drafting a complex answer using both tools. 

### Stage 1 - Environment Setup

* First, check you have access to the GPT3 playground [OpenAI GPT3 playground](https://beta.openai.com/playground). The screenshot for that page is 
![playground](images/playground.png)
* Then, check you have access to [Reasoner Coq website](https://coq.vercel.app/). The screenshot for that is 
![jscoq](images/jscoq.png)

### Stage 2 - Develop logic structure in the jsCoq scratchpad

* First, create a new scratchpad  [scratchpad link in jsCoq](https://coq.vercel.app/scratchpad.html), which can be launched on clicking the edit button middle top of the page. 

* Then, copy this below code to the left-hand side window


```

(** Helpers *)
Require Import String.

Inductive s: string->Prop:=
| str_(s':string): s s'
with tone: string->Prop:=
with original_text:string->Prop:=
with reason: string->Prop:=
with personal_experience: string->Prop:=
.


```

* Execute the DOWN button from the right-hand window

* You should see this screenshot at this stage: 
![initial batch](images/initial_batch.png)


