from openai import OpenAI
import os

client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

class LLM_Agent:
    def __init__(self, model: str = "gpt-4o"):
        """
        Initializes the OpenAI client with the selected model.

        Args:
            model_choice (str): Either "gpt-4o" or "o3-mini".
        """
        self.model = model
        
    def get_response(self, messages) -> str:
        """
        Sends a prompt to the OpenAI model and returns the response.

        Args:
            prompt (str): The input prompt.

        Returns:
            str: The model's response.
        """
        completion = client.chat.completions.create(
            model=self.model,
            messages=messages
        )

        return completion.choices[0].message.content

class Reasoning_Agent(LLM_Agent):
    def __init__(self, model: str = "o3-mini"):
        """
        Initializes the OpenAI client with the selected model.

        Args:
            model_choice (str): Either "gpt-4o" or "o3-mini".
        """
        self.model = model

# Example usage:
if __name__ == "__main__":
    agent = LLM_Agent(model="gpt-4o")
    messages = [
        {"role": "system", "content": "You are a helpful assistant."},
        {"role": "user", "content": "Can you explain the concept of recursion in programming?"}
    ]
    #response = agent.get_response(messages)
    #print(response)
    
    reasoning_agent = Reasoning_Agent(model="o3-mini")
    messages = [
        {"role": "system", "content": "You are a helpful assistant."},
        {"role": "user", "content": "Can you explain the concept of recursion in programming?"}
    ]
    solution = reasoning_agent.get_response(messages)
    print(solution)