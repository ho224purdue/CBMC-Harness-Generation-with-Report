import json
from django.shortcuts import render
from django.http import JsonResponse
from django.views.decorators.csrf import csrf_exempt
from .controllers.call import queryLLM
from .controllers.code_analysis.analysis import analyze

def initial(request):
    return JsonResponse({"message": "Server up and running!", "status": 200})

# use curl http://localhost:8000/prompt -H "Content-Type: application/json" -d '{"company": specified-company-here, "prompt": your-prompt-here}'
@csrf_exempt
def test_prompt(request):
    if request.method == "POST":
        try:
            if not request.body:
                return JsonResponse({"status": 400, "message": "Empty request body"})
            user_input = json.loads(request.body)
            company = user_input["company"]
            prompt = user_input["prompt"]
            response = queryLLM(company, prompt)
            status = 200 if response is not None else 400
            reply = response if response is not None else "An error has occurred at queryLLM function"
            return JsonResponse({"status": status, "reply": reply})
        except json.JSONDecodeError:
            return JsonResponse({"status": 400, "message": "JSON decoding error"})
    else:
        return JsonResponse({"status": 400, "message": "Please use a POST request!"})

# To call this API endpoint use:
# curl http://localhost:8000/generate -H "Content-Type: application/json" -d '{payload}'
@csrf_exempt
def generate(request):
    if request.method == "POST":
        try:
            if not request.body:
                return JsonResponse({"status": 400, "message": "Empty request body"})
            data = json.loads(request.body)
            parameters = analyze("openai", data)
            return JsonResponse({"status": 200, "message": "Data successfully received!"})
        except json.JSONDecodeError:
            return JsonResponse({"status": 400, "message": "JSON decoding error"})
    else:
        return JsonResponse({"status": 400, "message": "Please use a POST request"})


